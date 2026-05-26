# NIA Bit-Blasting Module Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Migrate BLAN's QF_NIA bit-blasting (space sizing + CNF encoding with Greedy-Addition chain sorting) into Zolver as `src/theory/arith/bit_blast/`, wired in as one full-effort stage of the NIA `Reasoner` pipeline.

**Architecture:** A self-contained `bit_blast` module: `BitVec` (two's-complement bit-vector over `SatLit`), `BitBlastEncoder` (CNF gates + width-growing add/sub/mul/pow + `relZero` comparisons), `PolyBitBlaster` (PolyId monomials → BitVec with Greedy-Addition sorting), `SpaceEstimator` (per-variable bit-width plan + `boxIsComplete`), and `BitBlastSolver` (owns an independent CaDiCaL, runs encode→solve→validate→refine). `NiaSolver::stageBitBlast` maps results into the pipeline. SAT is always re-validated by `IntegerModelValidator`; UNSAT is emitted only when the box is provably complete (all vars hard-bounded, so width-growing arithmetic is exact).

**Tech Stack:** C++17, GMP (`mpz_class`), CaDiCaL via `createSatSolver()`, libpoly via `PolynomialKernel::terms()`, doctest unit tests, `tools/run_regression.py` oracle regression.

**Design spec:** `docs/superpowers/specs/2026-05-26-nia-bit-blast-design.md`

**Per-task build/test note (WSL):** build with bounded parallelism — `cmake --build build -j 2` (unlimited `-j` can OOM WSL on this tree). Run a single unit test group with `./build/tests/zolver_unit_tests --test-case="<name>"`.

---

## Task 1: `BitVec` type + model readback

**Files:**
- Create: `src/theory/arith/bit_blast/BitVec.h`
- Test: `tests/unit/test_bit_blast.cpp`

- [ ] **Step 1: Write the failing test**

Create `tests/unit/test_bit_blast.cpp`:

```cpp
// Bit-blast module: BitVec readback + encoder ops + GA sorting + solver modes.
#include <doctest/doctest.h>
#include <gmpxx.h>
#include "sat/SatSolver.h"
#include "theory/arith/bit_blast/BitVec.h"

using namespace zolver;
using namespace zolver::bitblast;

TEST_CASE("BitVec: litValue reads polarity") {
    auto sat = createSatSolver();
    SatVar v = sat->newVar();
    sat->addClause({SatLit::positive(v)});   // force v = true
    REQUIRE(static_cast<int>(sat->solve()) ==
            static_cast<int>(SatSolver::SolveResult::Sat));
    CHECK(litValue(*sat, SatLit::positive(v)) == true);
    CHECK(litValue(*sat, SatLit::negative(v)) == false);
}

TEST_CASE("BitVec: readBitVec reconstructs two's-complement value") {
    auto sat = createSatSolver();
    // Build a 4-bit pattern for -3 = 1101 (LSB first: 1,0,1,1)
    auto force = [&](bool b) {
        SatVar v = sat->newVar();
        sat->addClause({b ? SatLit::positive(v) : SatLit::negative(v)});
        return SatLit::positive(v);
    };
    BitVec bv;
    bv.bits = { force(true), force(false), force(true), force(true) }; // -3
    REQUIRE(static_cast<int>(sat->solve()) ==
            static_cast<int>(SatSolver::SolveResult::Sat));
    CHECK(readBitVec(*sat, bv) == mpz_class(-3));
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cmake --build build -j 2`
Expected: FAIL — `BitVec.h: No such file or directory`.

- [ ] **Step 3: Write minimal implementation**

Create `src/theory/arith/bit_blast/BitVec.h`:

```cpp
#pragma once

#include "sat/SatSolver.h"
#include <gmpxx.h>
#include <vector>

namespace zolver::bitblast {

// Two's-complement bit-vector. bits[0] = LSB, bits.back() = MSB (sign bit,
// weight -2^(width-1)). Each bit is a SatLit in the owning SAT instance.
struct BitVec {
    std::vector<SatLit> bits;
    bool      isConst   = false;
    mpz_class constValue = 0;     // valid iff isConst

    unsigned width() const { return static_cast<unsigned>(bits.size()); }
    SatLit   sign()  const { return bits.back(); }
};

// A SatLit is satisfied iff the variable's value matches the literal polarity.
inline bool litValue(const SatSolver& sat, SatLit l) {
    return sat.value(l.var) == l.sign;
}

// Reconstruct the signed integer value of a solved bit-vector.
inline mpz_class readBitVec(const SatSolver& sat, const BitVec& bv) {
    mpz_class v = 0;
    unsigned w = bv.width();
    for (unsigned i = 0; i + 1 < w; ++i) {
        if (litValue(sat, bv.bits[i])) v += (mpz_class(1) << i);
    }
    if (w > 0 && litValue(sat, bv.bits[w - 1])) {
        v -= (mpz_class(1) << (w - 1));   // sign bit weight
    }
    return v;
}

} // namespace zolver::bitblast
```

- [ ] **Step 4: Run test to verify it passes**

Run: `cmake --build build -j 2 && ./build/tests/zolver_unit_tests --test-case="BitVec:*"`
Expected: PASS (2 test cases).

- [ ] **Step 5: Commit**

```bash
git add src/theory/arith/bit_blast/BitVec.h tests/unit/test_bit_blast.cpp
git commit -m "feat(bit_blast): add two's-complement BitVec + model readback"
```

---

## Task 2: `BitBlastEncoder` — constants & Tseitin gates

**Files:**
- Create: `src/theory/arith/bit_blast/BitBlastEncoder.h`
- Create: `src/theory/arith/bit_blast/BitBlastEncoder.cpp`
- Test: `tests/unit/test_bit_blast.cpp` (append)

- [ ] **Step 1: Write the failing test**

Append to `tests/unit/test_bit_blast.cpp`:

```cpp
#include "theory/arith/bit_blast/BitBlastEncoder.h"

TEST_CASE("Encoder: andGate truth table") {
    auto sat = createSatSolver();
    BitBlastEncoder enc(*sat);
    auto mk = [&](bool b){ SatVar v=sat->newVar();
        sat->addClause({b?SatLit::positive(v):SatLit::negative(v)}); return SatLit::positive(v); };
    SatLit c = enc.andGate(mk(true), mk(false));
    REQUIRE(static_cast<int>(sat->solve()) == static_cast<int>(SatSolver::SolveResult::Sat));
    CHECK(litValue(*sat, c) == false);
}

TEST_CASE("Encoder: mkConst roundtrips through readBitVec") {
    for (long val : {0L, 1L, -1L, 7L, -8L, 42L, -42L}) {
        auto sat = createSatSolver();
        BitBlastEncoder enc(*sat);
        BitVec bv = enc.mkConst(mpz_class(val));
        REQUIRE(static_cast<int>(sat->solve()) == static_cast<int>(SatSolver::SolveResult::Sat));
        CHECK(readBitVec(*sat, bv) == mpz_class(val));
    }
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cmake --build build -j 2`
Expected: FAIL — `BitBlastEncoder.h: No such file or directory`.

- [ ] **Step 3: Write minimal implementation**

Create `src/theory/arith/bit_blast/BitBlastEncoder.h`:

```cpp
#pragma once

#include "sat/SatSolver.h"
#include "theory/arith/bit_blast/BitVec.h"
#include "expr/types.h"          // Relation
#include <gmpxx.h>
#include <utility>

namespace zolver::bitblast {

// CNF encoder over an independent SAT instance. Two's-complement, width-growing
// arithmetic: add -> max(wa,wb)+1, mul -> wa+wb, so the encoded value is exact
// whenever leaf widths cover their domains. Non-owning reference to the SAT.
class BitBlastEncoder {
public:
    explicit BitBlastEncoder(SatSolver& sat);

    SatLit constTrue()  const { return true_; }
    SatLit constFalse() const { return false_; }

    BitVec mkConst(const mpz_class& v, unsigned minWidth = 0);
    BitVec mkVar(unsigned width);

    // Tseitin gates (each allocates one fresh var).
    SatLit andGate(SatLit a, SatLit b);
    SatLit orGate(SatLit a, SatLit b);
    SatLit xorGate(SatLit a, SatLit b);
    SatLit iteGate(SatLit s, SatLit t, SatLit e);

    // Arithmetic.
    BitVec add(const BitVec& a, const BitVec& b);    // width max+1
    BitVec neg(const BitVec& a);                     // width +1
    BitVec sub(const BitVec& a, const BitVec& b);
    BitVec mul(const BitVec& a, const BitVec& b);    // width wa+wb
    BitVec mulConst(const mpz_class& c, const BitVec& a);
    BitVec powConst(const BitVec& a, unsigned e);

    // Relations: every NIA constraint is `value rel 0`.
    SatLit isZero(const BitVec& a);
    SatLit eq(const BitVec& a, const BitVec& b);
    SatLit relZero(const BitVec& a, Relation rel);

    void assertLit(SatLit l);

private:
    SatSolver& sat_;
    SatLit true_;
    SatLit false_;

    static unsigned bitsForValue(const mpz_class& v);
    BitVec signExtend(const BitVec& a, unsigned width);
    std::pair<SatLit, SatLit> fullAdder(SatLit a, SatLit b, SatLit cin);
    BitVec addFixed(const BitVec& a, const BitVec& b, unsigned w); // truncates to w
};

} // namespace zolver::bitblast
```

Create `src/theory/arith/bit_blast/BitBlastEncoder.cpp`:

```cpp
#include "theory/arith/bit_blast/BitBlastEncoder.h"
#include <algorithm>

namespace zolver::bitblast {

BitBlastEncoder::BitBlastEncoder(SatSolver& sat) : sat_(sat) {
    SatVar t = sat_.newVar();
    sat_.addClause({SatLit::positive(t)});   // clamp t = true
    true_  = SatLit::positive(t);
    false_ = SatLit::negative(t);
}

unsigned BitBlastEncoder::bitsForValue(const mpz_class& v) {
    unsigned w = 1;
    while (true) {
        mpz_class lo = -(mpz_class(1) << (w - 1));
        mpz_class hi =  (mpz_class(1) << (w - 1)) - 1;
        if (v >= lo && v <= hi) return w;
        ++w;
    }
}

BitVec BitBlastEncoder::mkConst(const mpz_class& v, unsigned minWidth) {
    unsigned w = std::max(minWidth, bitsForValue(v));
    BitVec bv;
    bv.isConst = true;
    bv.constValue = v;
    bv.bits.resize(w);
    mpz_class t = v;
    if (t < 0) t += (mpz_class(1) << w);     // two's-complement pattern
    for (unsigned i = 0; i < w; ++i) {
        bv.bits[i] = mpz_tstbit(t.get_mpz_t(), i) ? true_ : false_;
    }
    return bv;
}

BitVec BitBlastEncoder::mkVar(unsigned width) {
    BitVec bv;
    bv.bits.resize(width);
    for (unsigned i = 0; i < width; ++i) bv.bits[i] = SatLit::positive(sat_.newVar());
    return bv;
}

SatLit BitBlastEncoder::andGate(SatLit a, SatLit b) {
    SatLit c = SatLit::positive(sat_.newVar());
    sat_.addClause({a.negated(), b.negated(), c});
    sat_.addClause({a, c.negated()});
    sat_.addClause({b, c.negated()});
    return c;
}

SatLit BitBlastEncoder::orGate(SatLit a, SatLit b) {
    SatLit c = SatLit::positive(sat_.newVar());
    sat_.addClause({a, b, c.negated()});
    sat_.addClause({a.negated(), c});
    sat_.addClause({b.negated(), c});
    return c;
}

SatLit BitBlastEncoder::xorGate(SatLit a, SatLit b) {
    SatLit c = SatLit::positive(sat_.newVar());
    sat_.addClause({a.negated(), b.negated(), c.negated()});
    sat_.addClause({a, b, c.negated()});
    sat_.addClause({a, b.negated(), c});
    sat_.addClause({a.negated(), b, c});
    return c;
}

SatLit BitBlastEncoder::iteGate(SatLit s, SatLit t, SatLit e) {
    SatLit c = SatLit::positive(sat_.newVar());
    sat_.addClause({s.negated(), t.negated(), c});
    sat_.addClause({s.negated(), t, c.negated()});
    sat_.addClause({s, e.negated(), c});
    sat_.addClause({s, e, c.negated()});
    return c;
}

void BitBlastEncoder::assertLit(SatLit l) { sat_.addClause({l}); }

// --- arithmetic and relations are added in later tasks ---

} // namespace zolver::bitblast
```

- [ ] **Step 4: Run test to verify it passes**

Run: `cmake --build build -j 2 && ./build/tests/zolver_unit_tests --test-case="Encoder:*"`
Expected: PASS (2 cases; CMake auto-globs the new `.cpp`).

- [ ] **Step 5: Commit**

```bash
git add src/theory/arith/bit_blast/BitBlastEncoder.h src/theory/arith/bit_blast/BitBlastEncoder.cpp tests/unit/test_bit_blast.cpp
git commit -m "feat(bit_blast): encoder constants + Tseitin gates"
```

---

## Task 3: Encoder — adder, neg, sub

**Files:**
- Modify: `src/theory/arith/bit_blast/BitBlastEncoder.cpp` (add method bodies before the closing namespace)
- Test: `tests/unit/test_bit_blast.cpp` (append)

- [ ] **Step 1: Write the failing test**

Append to `tests/unit/test_bit_blast.cpp`:

```cpp
TEST_CASE("Encoder: add of two constants") {
    for (auto pr : std::vector<std::pair<long,long>>{{3,4},{-3,4},{-5,-9},{0,0},{7,-8}}) {
        auto sat = createSatSolver();
        BitBlastEncoder enc(*sat);
        BitVec r = enc.add(enc.mkConst(mpz_class(pr.first)), enc.mkConst(mpz_class(pr.second)));
        REQUIRE(static_cast<int>(sat->solve()) == static_cast<int>(SatSolver::SolveResult::Sat));
        CHECK(readBitVec(*sat, r) == mpz_class(pr.first + pr.second));
    }
}

TEST_CASE("Encoder: sub and a free variable solve to a target") {
    auto sat = createSatSolver();
    BitBlastEncoder enc(*sat);
    BitVec x = enc.mkVar(6);                 // signed 6-bit
    BitVec d = enc.sub(x, enc.mkConst(mpz_class(10)));   // x - 10
    enc.assertLit(enc.isZero(d));            // force x - 10 == 0
    REQUIRE(static_cast<int>(sat->solve()) == static_cast<int>(SatSolver::SolveResult::Sat));
    CHECK(readBitVec(*sat, x) == mpz_class(10));
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cmake --build build -j 2`
Expected: FAIL — link error: undefined reference to `add`/`sub`/`isZero` (declared, not yet defined).

- [ ] **Step 3: Write minimal implementation**

In `BitBlastEncoder.cpp`, replace the `// --- arithmetic and relations are added in later tasks ---` comment line with:

```cpp
BitVec BitBlastEncoder::signExtend(const BitVec& a, unsigned width) {
    BitVec r = a;
    SatLit s = a.sign();
    while (r.bits.size() < width) r.bits.push_back(s);
    return r;
}

std::pair<SatLit, SatLit> BitBlastEncoder::fullAdder(SatLit a, SatLit b, SatLit cin) {
    SatLit axb  = xorGate(a, b);
    SatLit sum  = xorGate(axb, cin);
    SatLit ab   = andGate(a, b);
    SatLit acin = andGate(axb, cin);
    SatLit cout = orGate(ab, acin);
    return {sum, cout};
}

BitVec BitBlastEncoder::addFixed(const BitVec& a, const BitVec& b, unsigned w) {
    BitVec ea = signExtend(a, w), eb = signExtend(b, w);
    BitVec r; r.bits.resize(w);
    SatLit cin = false_;
    for (unsigned i = 0; i < w; ++i) {
        auto sc = fullAdder(ea.bits[i], eb.bits[i], cin);
        r.bits[i] = sc.first;
        cin = sc.second;
    }
    return r;   // final carry dropped (caller sized w to avoid overflow)
}

BitVec BitBlastEncoder::add(const BitVec& a, const BitVec& b) {
    unsigned w = std::max(a.width(), b.width()) + 1;
    return addFixed(a, b, w);
}

BitVec BitBlastEncoder::neg(const BitVec& a) {
    // Two's-complement negate: invert bits, then +1, in width a.width()+1
    // (one extra bit so that -(-2^(w-1)) = 2^(w-1) is representable).
    BitVec inv; inv.bits.resize(a.width());
    for (unsigned i = 0; i < a.width(); ++i) inv.bits[i] = a.bits[i].negated();
    return addFixed(inv, mkConst(mpz_class(1)), a.width() + 1);
}

BitVec BitBlastEncoder::sub(const BitVec& a, const BitVec& b) {
    return add(a, neg(b));
}

SatLit BitBlastEncoder::isZero(const BitVec& a) {
    SatLit acc = a.bits[0];
    for (unsigned i = 1; i < a.width(); ++i) acc = orGate(acc, a.bits[i]);
    return acc.negated();
}
```

- [ ] **Step 4: Run test to verify it passes**

Run: `cmake --build build -j 2 && ./build/tests/zolver_unit_tests --test-case="Encoder: add*,Encoder: sub*"`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add src/theory/arith/bit_blast/BitBlastEncoder.cpp tests/unit/test_bit_blast.cpp
git commit -m "feat(bit_blast): ripple-carry add/neg/sub + isZero"
```

---

## Task 4: Encoder — multiply, mulConst, powConst

**Files:**
- Modify: `src/theory/arith/bit_blast/BitBlastEncoder.cpp` (append before closing namespace)
- Test: `tests/unit/test_bit_blast.cpp` (append)

- [ ] **Step 1: Write the failing test**

Append to `tests/unit/test_bit_blast.cpp`:

```cpp
TEST_CASE("Encoder: mul of two constants (signed)") {
    for (auto pr : std::vector<std::pair<long,long>>{{3,4},{-3,4},{-5,-6},{0,9},{7,-8}}) {
        auto sat = createSatSolver();
        BitBlastEncoder enc(*sat);
        BitVec r = enc.mul(enc.mkConst(mpz_class(pr.first)), enc.mkConst(mpz_class(pr.second)));
        REQUIRE(static_cast<int>(sat->solve()) == static_cast<int>(SatSolver::SolveResult::Sat));
        CHECK(readBitVec(*sat, r) == mpz_class(pr.first) * mpz_class(pr.second));
    }
}

TEST_CASE("Encoder: powConst x^3 with x forced to -2") {
    auto sat = createSatSolver();
    BitBlastEncoder enc(*sat);
    BitVec x = enc.mkVar(5);
    enc.assertLit(enc.eq(x, enc.mkConst(mpz_class(-2))));
    BitVec c = enc.powConst(x, 3);                 // x^3
    REQUIRE(static_cast<int>(sat->solve()) == static_cast<int>(SatSolver::SolveResult::Sat));
    CHECK(readBitVec(*sat, c) == mpz_class(-8));
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cmake --build build -j 2`
Expected: FAIL — undefined reference to `mul`/`powConst`/`eq`.

- [ ] **Step 3: Write minimal implementation**

Append to `BitBlastEncoder.cpp` (before the final `} // namespace`):

```cpp
BitVec BitBlastEncoder::mul(const BitVec& a, const BitVec& b) {
    unsigned w = a.width() + b.width();
    BitVec ea = signExtend(a, w), eb = signExtend(b, w);
    BitVec acc = mkConst(mpz_class(0), w);
    for (unsigned i = 0; i < w; ++i) {
        BitVec partial; partial.bits.resize(w);
        for (unsigned j = 0; j < w; ++j) {
            partial.bits[j] = (j >= i) ? andGate(ea.bits[j - i], eb.bits[i]) : false_;
        }
        acc = addFixed(acc, partial, w);    // low w bits = exact signed product
    }
    return acc;
}

BitVec BitBlastEncoder::mulConst(const mpz_class& c, const BitVec& a) {
    if (c == 0) return mkConst(mpz_class(0), 1);
    if (a.isConst) return mkConst(c * a.constValue);
    return mul(mkConst(c), a);
}

BitVec BitBlastEncoder::powConst(const BitVec& a, unsigned e) {
    if (e == 0) return mkConst(mpz_class(1));
    BitVec r = a;
    for (unsigned i = 1; i < e; ++i) r = mul(r, a);
    return r;
}

SatLit BitBlastEncoder::eq(const BitVec& a, const BitVec& b) {
    return isZero(sub(a, b));
}
```

- [ ] **Step 4: Run test to verify it passes**

Run: `cmake --build build -j 2 && ./build/tests/zolver_unit_tests --test-case="Encoder: mul*,Encoder: powConst*"`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add src/theory/arith/bit_blast/BitBlastEncoder.cpp tests/unit/test_bit_blast.cpp
git commit -m "feat(bit_blast): shift-add signed multiply, mulConst, powConst"
```

---

## Task 5: Encoder — relation literals (`relZero`)

**Files:**
- Modify: `src/theory/arith/bit_blast/BitBlastEncoder.cpp` (append before closing namespace)
- Test: `tests/unit/test_bit_blast.cpp` (append)

- [ ] **Step 1: Write the failing test**

Append to `tests/unit/test_bit_blast.cpp`:

```cpp
TEST_CASE("Encoder: relZero Leq forces value <= 0") {
    auto sat = createSatSolver();
    BitBlastEncoder enc(*sat);
    BitVec x = enc.mkVar(5);
    enc.assertLit(enc.relZero(x, Relation::Leq));     // x <= 0
    enc.assertLit(enc.relZero(enc.add(x, enc.mkConst(mpz_class(3))), Relation::Geq)); // x+3 >= 0
    REQUIRE(static_cast<int>(sat->solve()) == static_cast<int>(SatSolver::SolveResult::Sat));
    mpz_class xv = readBitVec(*sat, x);
    CHECK(xv <= 0);
    CHECK(xv >= -3);
}

TEST_CASE("Encoder: relZero Geq + Leq pins value to 0 (Eq)") {
    auto sat = createSatSolver();
    BitBlastEncoder enc(*sat);
    BitVec x = enc.mkVar(5);
    enc.assertLit(enc.relZero(x, Relation::Eq));
    REQUIRE(static_cast<int>(sat->solve()) == static_cast<int>(SatSolver::SolveResult::Sat));
    CHECK(readBitVec(*sat, x) == 0);
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cmake --build build -j 2`
Expected: FAIL — undefined reference to `relZero`.

- [ ] **Step 3: Write minimal implementation**

Append to `BitBlastEncoder.cpp` (before the final `} // namespace`):

```cpp
SatLit BitBlastEncoder::relZero(const BitVec& a, Relation rel) {
    SatLit z = isZero(a);   // a == 0
    SatLit s = a.sign();    // a < 0  (exact, since `a` holds the value at full width)
    switch (rel) {
        case Relation::Eq:  return z;
        case Relation::Neq: return z.negated();
        case Relation::Lt:  return s;
        case Relation::Leq: return orGate(s, z);
        case Relation::Gt:  return andGate(s.negated(), z.negated());
        case Relation::Geq: return s.negated();
    }
    return z;
}
```

- [ ] **Step 4: Run test to verify it passes**

Run: `cmake --build build -j 2 && ./build/tests/zolver_unit_tests --test-case="Encoder: relZero*"`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add src/theory/arith/bit_blast/BitBlastEncoder.cpp tests/unit/test_bit_blast.cpp
git commit -m "feat(bit_blast): relZero signed comparison literals"
```

---

## Task 6: `PolyBitBlaster` — monomials → BitVec with Greedy-Addition sorting

**Files:**
- Create: `src/theory/arith/bit_blast/PolyBitBlaster.h`
- Create: `src/theory/arith/bit_blast/PolyBitBlaster.cpp`
- Test: `tests/unit/test_bit_blast.cpp` (append)

- [ ] **Step 1: Write the failing test**

Append to `tests/unit/test_bit_blast.cpp`:

```cpp
#include "theory/arith/bit_blast/PolyBitBlaster.h"
#include "theory/arith/poly/PolynomialKernel.h"

TEST_CASE("PolyBitBlaster: encode 2*x*y + 3 == 0 with x=3,y forced") {
    auto kernel = createPolynomialKernel();
    VarId vx = kernel->getOrCreateVar("x");
    VarId vy = kernel->getOrCreateVar("y");
    // poly = 2*x*y + 3
    PolyId xy = kernel->mul(kernel->mkVar(vx), kernel->mkVar(vy));
    PolyId poly = kernel->add(kernel->mul(kernel->mkConst(2), xy), kernel->mkConst(3));

    auto sat = createSatSolver();
    bitblast::BitBlastEncoder enc(*sat);
    std::unordered_map<std::string, bitblast::BitVec> vars;
    vars["x"] = enc.mkVar(6);
    vars["y"] = enc.mkVar(6);
    bitblast::PolyBitBlaster blaster(enc, *kernel, vars);
    // Force x = 3, then assert 2*x*y + 3 == 0  =>  6y + 3 == 0  => no integer y
    enc.assertLit(enc.eq(vars["x"], enc.mkConst(mpz_class(3))));
    blaster.assertConstraint({poly, Relation::Eq, SatLit{}});
    CHECK(static_cast<int>(sat->solve()) == static_cast<int>(SatSolver::SolveResult::Unsat));
}

TEST_CASE("PolyBitBlaster: Greedy-Addition narrows max intermediate width") {
    auto kernel = createPolynomialKernel();
    // Four equal-width 3-bit-ish leaves a+b+c+d. GA folds (a+b)+(c+d) => width 5,
    // unsorted left-fold ((a+b)+c)+d => width 6. We check the GA folded width.
    std::vector<std::string> names{"a","b","c","d"};
    auto sat = createSatSolver();
    bitblast::BitBlastEncoder enc(*sat);
    std::unordered_map<std::string, bitblast::BitVec> vars;
    PolyId sum = kernel->mkConst(0);
    for (auto& n : names) {
        VarId v = kernel->getOrCreateVar(n);
        vars[n] = enc.mkVar(3);
        sum = kernel->add(sum, kernel->mkVar(v));
    }
    bitblast::PolyBitBlaster blaster(enc, *kernel, vars);
    unsigned w = blaster.encodePolyWidth(sum);   // test-only accessor
    CHECK(w <= 5u);   // balanced GA tree, not the 6 of a linear chain
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cmake --build build -j 2`
Expected: FAIL — `PolyBitBlaster.h: No such file or directory`.

- [ ] **Step 3: Write minimal implementation**

Create `src/theory/arith/bit_blast/PolyBitBlaster.h`:

```cpp
#pragma once

#include "theory/arith/bit_blast/BitBlastEncoder.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include "theory/arith/nia/preprocess/NiaNormalizer.h"   // NormalizedNiaConstraint
#include <string>
#include <unordered_map>

namespace zolver::bitblast {

// Lowers a normalized NIA constraint `p rel 0` to CNF: decomposes p into
// monomials (kernel.terms), encodes each as coeff * prod(var^exp), then sums
// them with Greedy-Addition sorting (fold the two narrowest first) before
// asserting `relZero(sum, rel)`.
class PolyBitBlaster {
public:
    PolyBitBlaster(BitBlastEncoder& enc, PolynomialKernel& kernel,
                   const std::unordered_map<std::string, BitVec>& varBits);

    void assertConstraint(const NormalizedNiaConstraint& c);

    // Encode a polynomial to its value bit-vector (used by assertConstraint).
    BitVec encodePoly(PolyId p);

    // Test-only: width of the encoded value bit-vector.
    unsigned encodePolyWidth(PolyId p) { return encodePoly(p).width(); }

private:
    BitVec encodeMonomial(const PolynomialKernel::MonomialTerm& m);

    BitBlastEncoder& enc_;
    PolynomialKernel& kernel_;
    const std::unordered_map<std::string, BitVec>& varBits_;
};

} // namespace zolver::bitblast
```

Create `src/theory/arith/bit_blast/PolyBitBlaster.cpp`:

```cpp
#include "theory/arith/bit_blast/PolyBitBlaster.h"
#include <algorithm>

namespace zolver::bitblast {

PolyBitBlaster::PolyBitBlaster(BitBlastEncoder& enc, PolynomialKernel& kernel,
                               const std::unordered_map<std::string, BitVec>& varBits)
    : enc_(enc), kernel_(kernel), varBits_(varBits) {}

BitVec PolyBitBlaster::encodeMonomial(const PolynomialKernel::MonomialTerm& m) {
    if (m.powers.empty()) return enc_.mkConst(m.coefficient);
    BitVec prod;
    bool first = true;
    for (const auto& pe : m.powers) {
        std::string name(kernel_.varName(pe.first));
        const BitVec& vb = varBits_.at(name);
        BitVec powered = enc_.powConst(vb, static_cast<unsigned>(pe.second));
        prod = first ? powered : enc_.mul(prod, powered);
        first = false;
    }
    return enc_.mulConst(m.coefficient, prod);
}

BitVec PolyBitBlaster::encodePoly(PolyId p) {
    auto termsOpt = kernel_.terms(p);
    if (!termsOpt || termsOpt->empty()) return enc_.mkConst(mpz_class(0), 1);

    std::vector<BitVec> monos;
    monos.reserve(termsOpt->size());
    for (const auto& m : *termsOpt) monos.push_back(encodeMonomial(m));

    // Greedy Addition: repeatedly fold the two narrowest summands.
    while (monos.size() > 1) {
        std::sort(monos.begin(), monos.end(),
                  [](const BitVec& a, const BitVec& b) { return a.width() < b.width(); });
        BitVec s = enc_.add(monos[0], monos[1]);
        monos.erase(monos.begin(), monos.begin() + 2);
        monos.push_back(s);
    }
    return monos.front();
}

void PolyBitBlaster::assertConstraint(const NormalizedNiaConstraint& c) {
    BitVec value = encodePoly(c.poly);
    enc_.assertLit(enc_.relZero(value, c.rel));
}

} // namespace zolver::bitblast
```

- [ ] **Step 4: Run test to verify it passes**

Run: `cmake --build build -j 2 && ./build/tests/zolver_unit_tests --test-case="PolyBitBlaster:*"`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add src/theory/arith/bit_blast/PolyBitBlaster.h src/theory/arith/bit_blast/PolyBitBlaster.cpp tests/unit/test_bit_blast.cpp
git commit -m "feat(bit_blast): PolyBitBlaster with Greedy-Addition chain sorting"
```

---

## Task 7: `SpaceEstimator` — bit-width plan + `boxIsComplete`

**Files:**
- Create: `src/theory/arith/bit_blast/SpaceEstimator.h`
- Create: `src/theory/arith/bit_blast/SpaceEstimator.cpp`
- Test: `tests/unit/test_bit_blast.cpp` (append)

- [ ] **Step 1: Write the failing test**

Append to `tests/unit/test_bit_blast.cpp`:

```cpp
#include "theory/arith/bit_blast/SpaceEstimator.h"
#include "theory/arith/nia/core/DomainStore.h"

TEST_CASE("SpaceEstimator: bitsToCover") {
    using bitblast::SpaceEstimator;
    CHECK(SpaceEstimator::bitsToCover(mpz_class(0), mpz_class(0)) == 1u);   // {0}
    CHECK(SpaceEstimator::bitsToCover(mpz_class(-1), mpz_class(0)) == 1u);  // {-1,0}
    CHECK(SpaceEstimator::bitsToCover(mpz_class(0), mpz_class(7)) == 4u);   // 0..7 needs sign+3
    CHECK(SpaceEstimator::bitsToCover(mpz_class(-8), mpz_class(7)) == 4u);
}

TEST_CASE("SpaceEstimator: boxIsComplete only when all vars hard-bounded") {
    auto kernel = createPolynomialKernel();
    VarId vx = kernel->getOrCreateVar("x");
    VarId vy = kernel->getOrCreateVar("y");
    PolyId p = kernel->add(kernel->mkVar(vx), kernel->mkVar(vy));   // x + y
    std::vector<NormalizedNiaConstraint> cs{{p, Relation::Eq, SatLit{}}};

    bitblast::SpaceEstimator est(*kernel);

    DomainStore d1;     // only x bounded
    d1.addLowerBound("x", mpz_class(-4), SatLit{1, true});
    d1.addUpperBound("x", mpz_class(4),  SatLit{2, true});
    auto plan1 = est.estimate(cs, d1);
    CHECK(plan1.boxIsComplete == false);
    CHECK(plan1.width.count("x") == 1);
    CHECK(plan1.width.count("y") == 1);

    DomainStore d2;     // both bounded
    d2.addLowerBound("x", mpz_class(-4), SatLit{1, true});
    d2.addUpperBound("x", mpz_class(4),  SatLit{2, true});
    d2.addLowerBound("y", mpz_class(0),  SatLit{3, true});
    d2.addUpperBound("y", mpz_class(15), SatLit{4, true});
    auto plan2 = est.estimate(cs, d2);
    CHECK(plan2.boxIsComplete == true);
    CHECK(plan2.width.at("y") == SpaceEstimator::bitsToCover(mpz_class(0), mpz_class(15)));
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cmake --build build -j 2`
Expected: FAIL — `SpaceEstimator.h: No such file or directory`.

- [ ] **Step 3: Write minimal implementation**

Create `src/theory/arith/bit_blast/SpaceEstimator.h`:

```cpp
#pragma once

#include "theory/arith/poly/PolynomialKernel.h"
#include "theory/arith/nia/preprocess/NiaNormalizer.h"
#include "theory/arith/nia/core/DomainStore.h"
#include <gmpxx.h>
#include <string>
#include <unordered_map>
#include <vector>

namespace zolver::bitblast {

struct BitWidthPlan {
    std::unordered_map<std::string, unsigned> width;
    bool boxIsComplete = false;
};

// Part 1 ("where solutions can be"): per-variable bit-width sizing.
// Variable set = vars(cs) ∪ {vars carrying any DomainStore restriction}, so
// domain-only variables are still encoded/validated downstream. Hard-bounded
// vars get a width that exactly covers [lb,ub] (so width-growing arithmetic is
// overflow-free); unbounded vars get a heuristic width from coefficient
// magnitude (BLAN Coefficient-Matching) and multiplication count (BLAN
// Multiplication-Adaptation). boxIsComplete iff EVERY var in that set is
// hard-bounded.
class SpaceEstimator {
public:
    explicit SpaceEstimator(PolynomialKernel& kernel) : kernel_(kernel) {}

    BitWidthPlan estimate(const std::vector<NormalizedNiaConstraint>& cs,
                          const DomainStore& domains) const;

    // Smallest two's-complement width w with -2^(w-1) <= lo and hi <= 2^(w-1)-1.
    static unsigned bitsToCover(const mpz_class& lo, const mpz_class& hi);

    // Heuristic refinement: DOUBLE every width (capped at maxBW). Doubling lets
    // the loop reach large widths in a few iterations; an additive step with a
    // low iteration cap would leave a high maxBW unreachable.
    static BitWidthPlan grow(BitWidthPlan plan, unsigned maxBW);

private:
    PolynomialKernel& kernel_;
};

} // namespace zolver::bitblast
```

Create `src/theory/arith/bit_blast/SpaceEstimator.cpp`:

```cpp
#include "theory/arith/bit_blast/SpaceEstimator.h"
#include <algorithm>
#include <unordered_set>

namespace zolver::bitblast {

unsigned SpaceEstimator::bitsToCover(const mpz_class& lo, const mpz_class& hi) {
    unsigned w = 1;
    while (true) {
        mpz_class L = -(mpz_class(1) << (w - 1));
        mpz_class H =  (mpz_class(1) << (w - 1)) - 1;
        if (lo >= L && hi <= H) return w;
        ++w;
    }
}

BitWidthPlan SpaceEstimator::grow(BitWidthPlan plan, unsigned maxBW) {
    for (auto& kv : plan.width) kv.second = std::min(maxBW, kv.second * 2);
    return plan;
}

BitWidthPlan SpaceEstimator::estimate(const std::vector<NormalizedNiaConstraint>& cs,
                                      const DomainStore& domains) const {
    BitWidthPlan plan;
    std::unordered_set<std::string> vars;
    std::unordered_map<std::string, mpz_class> maxCoeff;
    unsigned mulCount = 0;

    for (const auto& c : cs) {
        auto t = kernel_.terms(c.poly);
        if (!t) {
            for (const auto& v : kernel_.variables(c.poly)) vars.insert(v);
            continue;
        }
        for (const auto& m : *t) {
            int deg = 0;
            for (const auto& pe : m.powers) deg += pe.second;
            if (deg >= 2) ++mulCount;
            for (const auto& pe : m.powers) {
                std::string n(kernel_.varName(pe.first));
                vars.insert(n);
                mpz_class ac = abs(m.coefficient);
                auto it = maxCoeff.find(n);
                if (it == maxCoeff.end() || ac > it->second) maxCoeff[n] = ac;
            }
        }
    }

    // Also include variables that appear ONLY in DomainStore restrictions (not
    // in any cs polynomial). They must be encoded and validated too, otherwise a
    // domain-only inconsistency (e.g. an empty domain on z) could be missed and
    // we'd return a spurious SAT. This makes the search self-contained.
    for (const auto& entry : domains.getAllDomains()) {
        const IntDomain& d = entry.second;
        bool restricted = d.hasLower || d.hasUpper || d.finiteValues || !d.excludedValues.empty();
        if (restricted) vars.insert(entry.first);
    }

    // Multiplication-Adaptation: shrink the heuristic base as products multiply.
    unsigned base = (mulCount > 64) ? 3u : (mulCount > 16 ? 4u : 6u);

    bool complete = true;
    for (const auto& v : vars) {
        const IntDomain* d = domains.getDomain(v);
        if (d && d->hasLower && d->hasUpper) {
            plan.width[v] = bitsToCover(d->lower.value, d->upper.value);
        } else {
            complete = false;
            unsigned cand = base;
            auto it = maxCoeff.find(v);
            if (it != maxCoeff.end() && it->second > 0) {
                unsigned cb = static_cast<unsigned>(
                    mpz_sizeinbase(it->second.get_mpz_t(), 2)) + 1;
                cand = std::max(cand, std::min(cb, 16u));   // Coefficient-Matching, capped K=16
            }
            plan.width[v] = cand;
        }
    }

    plan.boxIsComplete = complete && !vars.empty();
    return plan;
}

} // namespace zolver::bitblast
```

- [ ] **Step 4: Run test to verify it passes**

Run: `cmake --build build -j 2 && ./build/tests/zolver_unit_tests --test-case="SpaceEstimator:*"`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add src/theory/arith/bit_blast/SpaceEstimator.h src/theory/arith/bit_blast/SpaceEstimator.cpp tests/unit/test_bit_blast.cpp
git commit -m "feat(bit_blast): SpaceEstimator bit-width plan + boxIsComplete"
```

---

## Task 8: `BitBlastSolver` — orchestrator (encode → solve → validate → refine)

**Files:**
- Create: `src/theory/arith/bit_blast/BitBlastSolver.h`
- Create: `src/theory/arith/bit_blast/BitBlastSolver.cpp`
- Test: `tests/unit/test_bit_blast.cpp` (append)

- [ ] **Step 1: Write the failing test**

Append to `tests/unit/test_bit_blast.cpp`:

```cpp
#include "theory/arith/bit_blast/BitBlastSolver.h"
#include "theory/arith/nia/search/IntegerModelValidator.h"

// SOUNDNESS REGRESSION (reviewer's counterexample): bounds live ONLY in
// DomainStore, NOT in cs. The solver must still confine the search to the box
// (explicit bound encoding) and reject out-of-box models (modelInDomains).
// A naive "encode cs + validate cs" would wrongly accept x=-1,y=-6.
TEST_CASE("BitBlastSolver: SAT respects DomainStore bounds even when cs omits them") {
    auto kernel = createPolynomialKernel();
    VarId vx = kernel->getOrCreateVar("x");
    VarId vy = kernel->getOrCreateVar("y");
    PolyId prod = kernel->sub(kernel->mul(kernel->mkVar(vx), kernel->mkVar(vy)), kernel->mkConst(6));
    std::vector<NormalizedNiaConstraint> cs{{prod, Relation::Eq, SatLit{10, true}}}; // ONLY x*y-6==0
    DomainStore d;   // bounds ONLY here — never added to cs
    for (auto n : {"x","y"}) { d.addLowerBound(n, mpz_class(0), SatLit{11,true});
                               d.addUpperBound(n, mpz_class(6), SatLit{12,true}); }
    IntegerModelValidator validator(*kernel);
    bitblast::BitBlastSolver solver(*kernel);
    auto r = solver.solve(cs, d, validator);
    REQUIRE(r.status == bitblast::BitBlastResult::Status::Sat);
    CHECK(r.model.at("x") * r.model.at("y") == 6);
    CHECK(r.model.at("x") >= 0); CHECK(r.model.at("x") <= 6);   // box enforced, not just x*y=6
    CHECK(r.model.at("y") >= 0); CHECK(r.model.at("y") <= 6);   // would FAIL if x=-1,y=-6 accepted
}

TEST_CASE("BitBlastSolver: complete box UNSAT carries nonlinear AND bound reasons") {
    auto kernel = createPolynomialKernel();
    VarId vx = kernel->getOrCreateVar("x");
    // x*x = 2 has no integer root; x in [-3,3] (DomainStore) is the whole feasible box.
    PolyId sq = kernel->sub(kernel->pow(kernel->mkVar(vx), 2), kernel->mkConst(2));
    std::vector<NormalizedNiaConstraint> cs{{sq, Relation::Eq, SatLit{20, true}}}; // ONLY x*x-2==0
    DomainStore d;
    d.addLowerBound("x", mpz_class(-3), SatLit{21,true});
    d.addUpperBound("x", mpz_class(3),  SatLit{22,true});
    IntegerModelValidator validator(*kernel);
    bitblast::BitBlastSolver solver(*kernel);
    auto r = solver.solve(cs, d, validator);
    REQUIRE(r.status == bitblast::BitBlastResult::Status::UnsatComplete);
    REQUIRE(r.conflict.has_value());
    // Conflict must contain the nonlinear atom's reason (20) AND both bound
    // reasons (21,22) — UNSAT depends on the conjunction, not the interval alone.
    bool hasNonlinear = false, hasLower = false, hasUpper = false;
    for (const auto& l : r.conflict->clause) {
        if (l.var == 20) hasNonlinear = true;
        if (l.var == 21) hasLower = true;
        if (l.var == 22) hasUpper = true;
    }
    CHECK(hasNonlinear); CHECK(hasLower); CHECK(hasUpper);
}

TEST_CASE("BitBlastSolver: unbounded UNSAT returns Unknown, never UNSAT") {
    auto kernel = createPolynomialKernel();
    VarId vx = kernel->getOrCreateVar("x");
    PolyId p = kernel->sub(kernel->pow(kernel->mkVar(vx), 2), kernel->mkConst(2));
    std::vector<NormalizedNiaConstraint> cs{{p, Relation::Eq, SatLit{30, true}}};
    DomainStore d;   // x unbounded => boxIsComplete is false
    IntegerModelValidator validator(*kernel);
    bitblast::BitBlastSolver solver(*kernel);
    solver.setMaxIterations(2);   // keep the test fast; verdict is mode-invariant
    auto r = solver.solve(cs, d, validator);
    CHECK(r.status == bitblast::BitBlastResult::Status::Unknown);
}

// Point 1/3: a bound that was ENCODED but lacks a usable reason must force
// Unknown — never a partial (unsound) conflict.
TEST_CASE("BitBlastSolver: missing reason on an encoded bound => Unknown, not a bad conflict") {
    auto kernel = createPolynomialKernel();
    VarId vx = kernel->getOrCreateVar("x");
    PolyId p = kernel->sub(kernel->mkVar(vx), kernel->mkConst(5));      // x - 5
    std::vector<NormalizedNiaConstraint> cs{{p, Relation::Eq, SatLit{40, true}}}; // x == 5
    DomainStore d;
    d.addLowerBound("x", mpz_class(0), SatLit{41, true});
    d.addUpperBound("x", mpz_class(3), SatLit{});   // upper bound has NO usable reason (var 0)
    IntegerModelValidator validator(*kernel);
    bitblast::BitBlastSolver solver(*kernel);
    auto r = solver.solve(cs, d, validator);
    // x==5 with x in [0,3] is infeasible, but the upper bound is unjustified, so
    // we must NOT emit a conflict like (¬40 ∨ ¬41) — bail to Unknown instead.
    CHECK(r.status == bitblast::BitBlastResult::Status::Unknown);
}

// Point 2: a variable that appears ONLY in DomainStore (not in cs) is still
// encoded; a contradictory domain-only var must be detected (no spurious SAT).
TEST_CASE("BitBlastSolver: domain-only variable inconsistency is detected") {
    auto kernel = createPolynomialKernel();
    VarId vx = kernel->getOrCreateVar("x");
    VarId vy = kernel->getOrCreateVar("y");
    PolyId prod = kernel->sub(kernel->mul(kernel->mkVar(vx), kernel->mkVar(vy)), kernel->mkConst(6));
    std::vector<NormalizedNiaConstraint> cs{{prod, Relation::Eq, SatLit{50, true}}}; // only x,y in cs
    DomainStore d;
    for (auto n : {"x","y"}) { d.addLowerBound(n, mpz_class(0), SatLit{51,true});
                               d.addUpperBound(n, mpz_class(6), SatLit{52,true}); }
    // z appears ONLY in domains, with an empty interval [5,3] => whole state UNSAT.
    d.addLowerBound("z", mpz_class(5), SatLit{53,true});
    d.addUpperBound("z", mpz_class(3), SatLit{54,true});
    IntegerModelValidator validator(*kernel);
    bitblast::BitBlastSolver solver(*kernel);
    auto r = solver.solve(cs, d, validator);
    // Must NOT be Sat (a naive vars(cs)-only encoding would have returned Sat).
    CHECK(r.status != bitblast::BitBlastResult::Status::Sat);
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cmake --build build -j 2`
Expected: FAIL — `BitBlastSolver.h: No such file or directory`.

- [ ] **Step 3: Write minimal implementation**

Create `src/theory/arith/bit_blast/BitBlastSolver.h`:

```cpp
#pragma once

#include "theory/arith/bit_blast/SpaceEstimator.h"
#include "theory/arith/bit_blast/BitBlastEncoder.h"   // BitVec, BitBlastEncoder
#include "theory/arith/poly/PolynomialKernel.h"
#include "theory/arith/nia/preprocess/NiaNormalizer.h"
#include "theory/arith/nia/core/DomainStore.h"
#include "theory/arith/nia/search/IntegerModelValidator.h"
#include "theory/core/TheoryAtomTypes.h"   // TheoryConflict
#include <optional>
#include <string>
#include <unordered_map>
#include <vector>

namespace zolver::bitblast {

struct BitBlastResult {
    enum class Status { Sat, UnsatComplete, Unknown };
    Status status = Status::Unknown;
    IntegerModel model;                       // valid iff Sat
    std::optional<TheoryConflict> conflict;   // valid iff UnsatComplete
};

// Orchestrates one bit-blast attempt: size widths, encode over an independent
// CaDiCaL, solve, validate SAT, and refine widths in heuristic mode. Sound by
// construction (see design spec §2): SAT validated, UNSAT only when complete.
//
// SELF-CONTAINED SOUNDNESS: the solver encodes BOTH (a) every constraint in
// `cs` AND (b) the DomainStore hard bounds of each variable, so the SAT search
// space EQUALS the box [lb,ub]^n intersected with `cs` — it does not rely on
// `cs` happening to contain the bound atoms. A SAT model is accepted only if it
// passes IntegerModelValidator over `cs` AND lies inside the DomainStore box
// (`modelInDomains`). UNSAT is emitted only when `boxIsComplete`, with a
// conflict over the reasons of BOTH the cs constraints and the domain bounds.
class BitBlastSolver {
public:
    explicit BitBlastSolver(PolynomialKernel& kernel)
        : kernel_(kernel), estimator_(kernel) {}

    BitBlastResult solve(const std::vector<NormalizedNiaConstraint>& cs,
                         const DomainStore& domains,
                         const IntegerModelValidator& validator);

    void setMaxBitWidth(unsigned w) { maxBW_ = w; }
    void setMaxIterations(unsigned n) { maxIters_ = n; }

private:
    bool applicable(const std::vector<NormalizedNiaConstraint>& cs) const;

    // Encode `x >= lb` and `x <= ub` (and finite-set / exclusions) for every
    // bounded variable, so the SAT search is confined to the DomainStore box.
    void encodeDomainBounds(BitBlastEncoder& enc,
                            const std::unordered_map<std::string, BitVec>& varBits,
                            const DomainStore& domains);

    // Independent check that a candidate model lies inside the DomainStore box
    // (bounds, finite sets, exclusions). Belt-and-suspenders with the encoding.
    static bool modelInDomains(const IntegerModel& model, const DomainStore& domains);

    // Conflict = negated reasons of EVERY encoded justification: all cs
    // constraints AND all domain bounds (the box participates in the UNSAT).
    // Returns nullopt if no usable reason literal exists, or if the clause is
    // self-contradictory.
    std::optional<TheoryConflict> buildCompleteConflict(
        const std::vector<NormalizedNiaConstraint>& cs, const DomainStore& domains) const;

    PolynomialKernel& kernel_;
    SpaceEstimator estimator_;
    unsigned maxBW_ = 256;     // QF_NIA: large solutions need headroom
    unsigned maxIters_ = 6;    // with doubling growth, reaches up to maxBW_
};

} // namespace zolver::bitblast
```

Create `src/theory/arith/bit_blast/BitBlastSolver.cpp`:

```cpp
#include "theory/arith/bit_blast/BitBlastSolver.h"
#include "theory/arith/bit_blast/BitBlastEncoder.h"
#include "theory/arith/bit_blast/PolyBitBlaster.h"
#include "sat/SatSolver.h"
#include <string>
#include <unordered_map>

namespace zolver::bitblast {

bool BitBlastSolver::applicable(const std::vector<NormalizedNiaConstraint>& cs) const {
    for (const auto& c : cs) {
        if (!kernel_.terms(c.poly)) return false;   // need monomial decomposition
    }
    return true;
}

void BitBlastSolver::encodeDomainBounds(
    BitBlastEncoder& enc,
    const std::unordered_map<std::string, BitVec>& varBits,
    const DomainStore& domains) {
    // Confine the SAT search to the DomainStore box so the search space EQUALS
    // [lb,ub]^n ∩ cs (not the raw two's-complement width range).
    for (const auto& kv : varBits) {
        const IntDomain* d = domains.getDomain(kv.first);
        if (!d) continue;
        const BitVec& x = kv.second;
        if (d->hasLower) {  // x >= lb  <=>  (x - lb) >= 0
            enc.assertLit(enc.relZero(enc.sub(x, enc.mkConst(d->lower.value)), Relation::Geq));
        }
        if (d->hasUpper) {  // x <= ub  <=>  (x - ub) <= 0
            enc.assertLit(enc.relZero(enc.sub(x, enc.mkConst(d->upper.value)), Relation::Leq));
        }
        if (d->finiteValues) {  // x ∈ {v1,...}  <=>  OR_i (x == vi)
            std::vector<SatLit> disj;
            for (const auto& v : *d->finiteValues)
                disj.push_back(enc.eq(x, enc.mkConst(v)));
            if (disj.empty()) { enc.assertLit(enc.constFalse()); }   // empty set => UNSAT
            else {
                SatLit acc = disj[0];
                for (size_t i = 1; i < disj.size(); ++i) acc = enc.orGate(acc, disj[i]);
                enc.assertLit(acc);
            }
        }
        for (const auto& ex : d->excludedValues) {  // x != v
            enc.assertLit(enc.relZero(enc.sub(x, enc.mkConst(ex.first)), Relation::Neq));
        }
    }
}

bool BitBlastSolver::modelInDomains(const IntegerModel& model, const DomainStore& domains) {
    for (const auto& entry : domains.getAllDomains()) {
        const std::string& var = entry.first;
        const IntDomain& d = entry.second;
        auto it = model.find(var);
        if (it == model.end()) continue;            // var not encoded; nothing to check
        const mpz_class& v = it->second;
        if (d.hasLower && v < d.lower.value) return false;
        if (d.hasUpper && v > d.upper.value) return false;
        if (d.finiteValues && d.finiteValues->count(v) == 0) return false;
        if (d.excludedValues.count(v)) return false;
    }
    return true;
}

std::optional<TheoryConflict> BitBlastSolver::buildCompleteConflict(
    const std::vector<NormalizedNiaConstraint>& cs, const DomainStore& domains) const {
    // The encoded conjunction (all cs constraints AND every encoded domain
    // restriction) is infeasible over the complete box, so the negation of
    // EVERY justifying reason literal is a sound theory lemma. CRITICAL: every
    // restriction we encoded must contribute its reason. If any encoded
    // restriction has NO usable reason, we cannot prove the conjunction sound —
    // silently dropping it would yield an UNSOUND conflict (e.g. "¬A ∨ ¬B" when
    // the real infeasibility also needed an unjustified bound). So we bail to
    // Unknown rather than emit a partial conflict.
    TheoryConflict cf;

    // A list of reason literals is usable iff it is non-empty and every literal
    // is a real variable; push their negations, or signal failure.
    auto pushAll = [&](const std::vector<SatLit>& reasons) -> bool {
        if (reasons.empty()) return false;
        for (const auto& l : reasons) {
            if (l.var == 0) return false;
            cf.clause.push_back(l.negated());
        }
        return true;
    };
    auto pushOne = [&](SatLit l) -> bool {
        if (l.var == 0) return false;
        cf.clause.push_back(l.negated());
        return true;
    };

    // (1) every cs constraint was encoded; each must carry a reason.
    for (const auto& c : cs) {
        if (!pushOne(c.reason)) return std::nullopt;
    }
    // (2) every encoded domain restriction (mirrors encodeDomainBounds) must
    //     carry a reason. Only restrictions actually present were encoded.
    for (const auto& entry : domains.getAllDomains()) {
        const IntDomain& d = entry.second;
        if (d.hasLower && !pushAll(d.lower.reasons)) return std::nullopt;
        if (d.hasUpper && !pushAll(d.upper.reasons)) return std::nullopt;
        if (d.finiteValues && !pushAll(d.finiteSetReasons)) return std::nullopt;
        for (const auto& ex : d.excludedValues) {
            if (!pushAll(ex.second)) return std::nullopt;
        }
    }

    if (cf.clause.empty()) return std::nullopt;                 // nothing to justify
    if (!normalizeTheoryClause(cf.clause)) return std::nullopt; // self-contradictory => bail
    return cf;
}

BitBlastResult BitBlastSolver::solve(const std::vector<NormalizedNiaConstraint>& cs,
                                     const DomainStore& domains,
                                     const IntegerModelValidator& validator) {
    BitBlastResult out;
    if (cs.empty() || !applicable(cs)) return out;   // Unknown

    BitWidthPlan plan = estimator_.estimate(cs, domains);
    if (plan.width.empty()) return out;              // Unknown

    for (unsigned iter = 0; iter < maxIters_; ++iter) {
        auto sat = createSatSolver();
        BitBlastEncoder enc(*sat);
        std::unordered_map<std::string, BitVec> varBits;
        for (const auto& kv : plan.width) varBits[kv.first] = enc.mkVar(kv.second);

        PolyBitBlaster blaster(enc, kernel_, varBits);
        for (const auto& c : cs) blaster.assertConstraint(c);
        encodeDomainBounds(enc, varBits, domains);   // confine search to the box

        auto res = sat->solve();
        if (res == SatSolver::SolveResult::Sat) {
            IntegerModel model;
            for (const auto& kv : varBits) model[kv.first] = readBitVec(*sat, kv.second);
            // Accept only a model that satisfies cs (exact) AND lies in the box.
            if (validator.validate(model, cs) == IntegerModelValidator::Result::Valid
                && modelInDomains(model, domains)) {
                out.status = BitBlastResult::Status::Sat;
                out.model = std::move(model);
                return out;
            }
            // SAT under narrow widths but not a real / in-box model: artifact.
        } else if (res == SatSolver::SolveResult::Unsat) {
            if (plan.boxIsComplete) {
                if (auto cf = buildCompleteConflict(cs, domains)) {
                    out.status = BitBlastResult::Status::UnsatComplete;
                    out.conflict = std::move(cf);
                }
                return out;   // complete box decided (UnsatComplete or Unknown if no reasons)
            }
            // Heuristic box UNSAT proves nothing globally: keep Unknown.
        } else {
            return out;       // SAT solver Unknown
        }

        if (plan.boxIsComplete) break;          // exact box already decided above
        plan = SpaceEstimator::grow(plan, maxBW_);   // doubling widen
    }
    return out;               // Unknown
}

} // namespace zolver::bitblast
```

- [ ] **Step 4: Run test to verify it passes**

Run: `cmake --build build -j 2 && ./build/tests/zolver_unit_tests --test-case="BitBlastSolver:*"`
Expected: PASS (3 cases).

- [ ] **Step 5: Commit**

```bash
git add src/theory/arith/bit_blast/BitBlastSolver.h src/theory/arith/bit_blast/BitBlastSolver.cpp tests/unit/test_bit_blast.cpp
git commit -m "feat(bit_blast): BitBlastSolver orchestrator with sound SAT/UNSAT contract"
```

---

## Task 9: Wire `stageBitBlast` into the NIA pipeline

**Files:**
- Modify: `src/theory/arith/ArithSolverBase.h` (add `reasonerNames()` introspection accessor)
- Modify: `src/theory/arith/nia/NiaSolver.h:15` (add include), `:121-122` (add member), `:146-147` (add stage decl)
- Modify: `src/theory/arith/nia/NiaSolver.cpp:21-33` (init member), `:55-56` (register stage), and append the stage body near line 499
- Test: `tests/unit/test_bit_blast.cpp` (append registration test)

- [ ] **Step 1: Write the failing test**

Append to `tests/unit/test_bit_blast.cpp`:

```cpp
#include "theory/arith/nia/NiaSolver.h"
#include <algorithm>

// Real registration check: the bit-blast stage must appear by name in the NIA
// reasoner pipeline, immediately AFTER "nia.bounded" and BEFORE
// "nia.local-search". A construct-and-check-id() test would pass even without
// the stage, so we introspect the pipeline order instead.
TEST_CASE("NiaSolver: bit-blast stage registered between bounded and local-search") {
    auto kernel = createPolynomialKernel();
    NiaSolver solver(std::move(kernel));
    auto names = solver.reasonerNames();
    auto bb = std::find(names.begin(), names.end(), "nia.bit-blast");
    auto bd = std::find(names.begin(), names.end(), "nia.bounded");
    auto ls = std::find(names.begin(), names.end(), "nia.local-search");
    REQUIRE(bb != names.end());
    REQUIRE(bd != names.end());
    REQUIRE(ls != names.end());
    CHECK(bd < bb);    // after bounded
    CHECK(bb < ls);    // before local-search
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cmake --build build -j 2`
Expected: FAIL — `NiaSolver` has no member `reasonerNames` (and the stage is not yet registered). Both are fixed in Step 3.

- [ ] **Step 3: Write minimal implementation**

In `src/theory/arith/ArithSolverBase.h`, add a public introspection accessor (place it next to the existing public methods, near the `check()` declaration around line 86):

```cpp
    // Names of the registered reasoner stages, in pipeline order. For testing
    // and diagnostics; reflects the order stages run in check().
    std::vector<std::string> reasonerNames() const {
        std::vector<std::string> names;
        names.reserve(reasoners_.size());
        for (const auto& r : reasoners_) names.push_back(r->name());
        return names;
    }
```

(If `<string>` / `<vector>` are not already included in `ArithSolverBase.h`, add them.)

In `src/theory/arith/nia/NiaSolver.h`, add the include after line 16 (`#include "theory/arith/nia/search/NiaLocalSearch.h"`):

```cpp
#include "theory/arith/bit_blast/BitBlastSolver.h"
```

In `src/theory/arith/nia/NiaSolver.h`, add a member after line 122 (`NiaLocalSearch localSearch_;`):

```cpp
    bitblast::BitBlastSolver bitBlast_;
    bool enableBitBlast_ = true;
```

In `src/theory/arith/nia/NiaSolver.h`, add the stage declaration after line 146 (`std::optional<TheoryCheckResult> stageBounded(...)`):

```cpp
    std::optional<TheoryCheckResult> stageBitBlast(TheoryLemmaStorage&, TheoryEffort);
```

In `src/theory/arith/nia/NiaSolver.cpp`, add to the constructor initializer list after `localSearch_(*kernel_)` (line 33) — insert a comma and:

```cpp
      localSearch_(*kernel_),
      bitBlast_(*kernel_) {
```

(Replace the existing `localSearch_(*kernel_) {` opening brace line accordingly.)

In `src/theory/arith/nia/NiaSolver.cpp`, in the constructor body, add a full-effort registration helper after the `add` lambda (after line 43) and register the stage between `nia.bounded` and `nia.local-search`:

```cpp
    auto addFull = [this](const char* nm,
                      std::optional<TheoryCheckResult> (NiaSolver::*m)(TheoryLemmaStorage&, TheoryEffort)) {
        reasoners_.push_back(std::make_unique<CallbackReasoner>(
            nm, [this, m](TheoryLemmaStorage& db, TheoryEffort e) { return (this->*m)(db, e); },
            /*fullEffortOnly=*/true));
    };
```

Then change the registration block so that after `add("nia.bounded", &NiaSolver::stageBounded);` (line 55) the next line is:

```cpp
    addFull("nia.bit-blast",  &NiaSolver::stageBitBlast);
```

(Keep `add("nia.local-search", &NiaSolver::stageLocalSearch);` immediately after it.)

In `src/theory/arith/nia/NiaSolver.cpp`, append the stage body immediately after `stageBounded` ends (after line 499, before `stageLocalSearch`):

```cpp
std::optional<TheoryCheckResult> NiaSolver::stageBitBlast(TheoryLemmaStorage&, TheoryEffort) {
    if (!enableBitBlast_) return std::nullopt;
    auto res = bitBlast_.solve(normalized_, domains_, validator_);
    switch (res.status) {
        case bitblast::BitBlastResult::Status::Sat:
            currentModel_ = res.model;
            return TheoryCheckResult::consistent();
        case bitblast::BitBlastResult::Status::UnsatComplete:
            return TheoryCheckResult::mkConflict(*res.conflict);
        case bitblast::BitBlastResult::Status::Unknown:
            return std::nullopt;
    }
    return std::nullopt;
}
```

- [ ] **Step 4: Run test to verify it passes**

Run: `cmake --build build -j 2 && ./build/tests/zolver_unit_tests --test-case="NiaSolver: bit-blast*"`
Expected: PASS. Then run the full unit suite to confirm no regression:
Run: `./build/tests/zolver_unit_tests`
Expected: all cases pass (≥523 pre-existing + the new bit_blast cases).

- [ ] **Step 5: Behavioral smoke check through the CLI**

Confirm the wired pipeline solves a bounded NIA instance end-to-end (verifies the stage participates without breaking the pipeline):

```bash
cat > /tmp/bb_smoke.smt2 <<'EOF'
(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (>= x 0)) (assert (<= x 6))
(assert (>= y 0)) (assert (<= y 6))
(assert (= (* x y) 6))
(check-sat)
EOF
./build/bin/zolver solve /tmp/bb_smoke.smt2
```
Expected: prints `sat` (no crash, no `unknown`). Formal per-stage soundness is gated in Task 10.

- [ ] **Step 6: Commit**

```bash
git add src/theory/arith/ArithSolverBase.h src/theory/arith/nia/NiaSolver.h src/theory/arith/nia/NiaSolver.cpp tests/unit/test_bit_blast.cpp
git commit -m "feat(nia): register full-effort bit-blast stage after bounded enumeration"
```

---

## Task 10: Regression cases + soundness gate

**Files:**
- Create: `tests/regression/nia/nia_<NNN>_sat_bitblast_product.smt2`
- Create: `tests/regression/nia/nia_<NNN+1>_unsat_bitblast_square.smt2`
- Create: `tests/regression/nia/nia_<NNN+2>_sat_bitblast_addchain.smt2`

- [ ] **Step 1: Pick the next free case numbers**

Run: `ls tests/regression/nia | sort | tail -5`
Expected: shows the current highest `nia_NNN_*` number; use the next three integers as `<NNN>`, `<NNN+1>`, `<NNN+2>` in the filenames below.

- [ ] **Step 2: Create the SAT product case**

Create `tests/regression/nia/nia_<NNN>_sat_bitblast_product.smt2`:

```smt2
(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (>= x 0)) (assert (<= x 6))
(assert (>= y 0)) (assert (<= y 6))
(assert (= (* x y) 6))
(check-sat)
```

- [ ] **Step 3: Create the complete-box UNSAT case**

Create `tests/regression/nia/nia_<NNN+1>_unsat_bitblast_square.smt2`:

```smt2
(set-logic QF_NIA)
(declare-fun x () Int)
(assert (>= x (- 3))) (assert (<= x 3))
(assert (= (* x x) 2))
(check-sat)
```

- [ ] **Step 4: Create the addition-chain SAT case**

Create `tests/regression/nia/nia_<NNN+2>_sat_bitblast_addchain.smt2`:

```smt2
(set-logic QF_NIA)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun c () Int)
(declare-fun d () Int)
(assert (>= a 0)) (assert (<= a 3))
(assert (>= b 0)) (assert (<= b 3))
(assert (>= c 0)) (assert (<= c 3))
(assert (>= d 0)) (assert (<= d 3))
(assert (= (+ (* a b) (* b c) (* c d) (* d a)) 12))
(check-sat)
```

- [ ] **Step 5: Run the NIA regression suite + verify soundness**

Run:
```bash
python3 tools/run_regression.py --root tests/regression --logic nia \
    --solver build/bin/zolver --timeout 20 -j 2
```
Expected: the three new cases match the z3/cvc5 oracle (`sat`, `unsat`, `sat`); **0 UNSOUND**; no previously-passing NIA case regresses. If a new case shows `unknown`, that is acceptable (not unsound) but investigate width sizing; if it shows the *wrong* verdict, STOP — that is an UNSOUND result and must be fixed before commit.

- [ ] **Step 6: A/B confirm the stage is actually exercised (behavioral value)**

The `reasonerNames` unit test (Task 9) proves the stage is *registered*; this
step proves it *affects results* and isn't shadowed by earlier stages. In
`src/theory/arith/nia/NiaSolver.h`, temporarily change `bool enableBitBlast_ =
true;` to `false`, rebuild, and re-run the three new cases:

```bash
# with enableBitBlast_ = false (temporary):
cmake --build build -j 2
for f in tests/regression/nia/nia_*_bitblast_*.smt2; do echo "$f:"; ./build/bin/zolver solve "$f"; done
```
Expected: at least one of the three flips to `unknown` (or a slower verdict),
demonstrating the stage contributes. **Restore `enableBitBlast_ = true`** and
rebuild before proceeding. (If nothing changes, the cases are already solved by
earlier stages — pick a harder bounded instance so the new stage is genuinely
exercised, otherwise the regression cases add no coverage for this feature.)

- [ ] **Step 7: Run the full gate**

Run:
```bash
cmake --build build -j 2 && ctest --test-dir build
```
Expected: `ctest` 15/15 labels pass (unit + all per-logic regression); baseline preserved.

- [ ] **Step 8: Commit**

```bash
git add tests/regression/nia/nia_*_bitblast_*.smt2
git commit -m "test(nia): bit-blast regression cases (sat product, unsat square, sat add-chain)"
```

---

## Self-Review notes (for the executor)

- **Spec coverage:** Part 1 (space sizing) = Task 7; Part 2 (bit-blast + Greedy-Addition) = Tasks 1–6; orchestration/soundness contract = Task 8; pipeline wiring = Task 9; soundness gate = Task 10. The excluded scope (Resolver/ICP/extra comparison modes) is intentionally absent.
- **Self-contained encoding (spec §2.0):** `BitBlastSolver` encodes BOTH every constraint in `cs` AND the `DomainStore` restrictions (`encodeDomainBounds`), over the variable set `vars(cs) ∪ restricted-domain-vars`, so the SAT search space EQUALS `[lb,ub]ⁿ ∩ cs` and domain-only variables are encoded too. A SAT model is accepted only if `validate(model, cs) == Valid` AND `modelInDomains(model, domains)`. Task 8 tests prove: bounds-only-in-`DomainStore` is still enforced (rejects `x=-1,y=-6`), and a domain-only contradictory `z` is detected (no spurious SAT).
- **Soundness invariants:** SAT requires both acceptance checks (exact `cs` validation + in-box). UNSAT is emitted only when `plan.boxIsComplete` AND a conflict can be built. The conflict (`buildCompleteConflict(cs, domains)`) is `⋁ ¬reason` over **every encoded justification** — all `cs` constraints (incl. nonlinear atoms) AND every encoded `DomainStore` restriction (lower/upper/finite/exclusion). **If ANY encoded justification lacks a usable reason it bails to Unknown — it never silently drops a reason** (that would make a partial, unsound conflict like `¬A∨¬B`). Empty/self-contradictory clause ⇒ Unknown. Never returns UNSAT from a heuristic box.
- **Type consistency:** `BitVec`, `BitBlastEncoder`, `PolyBitBlaster`, `BitWidthPlan`/`SpaceEstimator`, `BitBlastResult`/`BitBlastSolver` names and signatures are used identically across tasks; all live in `namespace zolver::bitblast`. `NiaSolver` refers to them as `bitblast::BitBlastSolver` / `bitblast::BitBlastResult`.
- **Build:** no CMake edits — `src/CMakeLists.txt` globs `theory/**/*.cpp` and `tests/CMakeLists.txt` globs `unit/*.cpp`.
- **WSL:** always build with `-j 2`.
