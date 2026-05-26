# Simplex-Enhanced CDCAC — Phase 1: Simplex-Guided Variable Ordering Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.
>
> **Revised 2026-05-27 after master review (four rounds).** Round-4 pre-execution fixes: (a) Task 2 adds an **end-to-end test** proving a row-derived bound reaches the facts for an *original* variable (construction forces `x` basic), guarding against the module degrading to stored-bounds+participation; (b) Task 4 uses `kernel.findVar` (const) instead of the non-const `getOrCreateVar` — the selector looks up existing VarIds, never mints them; (c) Task 2 evaluates *constant* linear atoms (`constant rel 0`) and sets `linearSubsetUnsat()` on a false one instead of silently extracting facts. Final shape: (1) Task 2 = **`SimplexTableauFacts`** — build a *fresh* `GeneralSimplex` over the active linear subset, and on SAT extract **read-only one-shot solved-tableau facts** (stored bounds + per-basic-variable interval derived from one pass over its tableau row + fixedness + basis/row/tight-slack participation + model value). Facts-only: it never returns a conflict, never short-circuits CDCAC, never affects the verdict. (2) `linearizationGain` uses residual-degree-after-fixing. (3) the new order is *degree-stratified* — ascending total degree is the primary key (preserving the `18bd5e0` soundness mitigation); `frontScore` tie-breaks only within equal-degree strata. (4) Task 0 probes expanded with disequality/distinct/mixed-equality. (5) soundness invariant and Task 6 promotion gate reworded to not claim verdict-invariance or monotone verdict count.

**Goal:** Within each equal-total-degree stratum of CDCAC's variable order — where the current order is arbitrary — order variables by a `frontScore` built from polynomial structure and **read-only facts from a solved Simplex tableau**, to reduce the NRA timeout/unknown gap (panda2: 27% timeout + 24% unknown) without perturbing the degree-based soundness mitigation already on `agent/a2-nonlinear`.

**Architecture:** A new `nra/simplex/` module computes two fact sets over the active constraints: (1) `PolyStructureFacts` — per-variable linearization gain / nonlinear connectivity / max degree from `kernel.terms()`; (2) `SimplexTableauFacts` — builds a *fresh* `GeneralSimplex` from the linear subset, runs one `check()`, and on SAT reads (without mutating) the solved tableau: stored finite bounds, one-shot intervals for basic variables (`xb = rhs + Σ aᵢ·xᵢ` evaluated over the non-basic vars' stored bounds), fixedness, basic/non-basic status, row & tight-row participation, and the model value. A selector keeps **ascending total degree as the primary sort key** (identical to the existing `ZOLVER_NRA_VARORDER`) and uses `frontScore` from those facts to break ties *within* equal-degree groups. Gated behind a new default-OFF flag `ZOLVER_NRA_VARORDER_SIMPLEX`; the existing `ZOLVER_NRA_VARORDER` and the OFF path are untouched.

**Tech Stack:** C++17, libpoly-backed `PolynomialKernel` (`kernel.terms()`, `kernel.degree()`), `GeneralSimplex` + `SparseTableau` (Dutertre–de Moura, `src/theory/arith/lra/`), GMP (`mpq_class`/`mpz_class`), doctest unit tests, SMT-LIB2 regression vs z3/cvc5 oracle.

---

## Scope

**In scope (this plan):** spec priority P2 (variable ordering), guided by polynomial structure + read-only solved-tableau facts from a fresh Simplex over the linear subset.

**The fact-extraction boundary (master decision — exact):** `SimplexTableauFacts` is **one-shot solved-tableau observation, not a propagation engine**. After a SAT Simplex `check()` it may:
- read stored finite lower/upper bounds from `varState`;
- for a basic variable `xb` with tableau row `xb = rhs + Σ aᵢ·xᵢ`, derive **one** interval for `xb` from the *currently stored* bounds of the non-basic `xᵢ` (interval arithmetic; if a needed bound is missing, skip that side);
- intersect that derived interval with `xb`'s stored bounds;
- mark fixedness when lower == upper;
- record basic/non-basic status, row participation, tight-row/zero-slack participation, and the model value.

It **must not**: (a) iterate to a fixpoint; (b) chain a derived basic-variable bound into other rows; (c) do reverse (basic→non-basic) inference; (d) run per-variable min/max LP; (e) use any derived fact for pruning or to change a verdict; (f) emit a SAT-level lemma/conflict.

**Facts-only on UNSAT (master decision):** if the fresh Simplex finds the linear subset UNSAT, `SimplexTableauFacts` returns **no ordering facts** (a diagnostic flag `linearSubsetUnsat()` only) and **does not** produce a conflict or short-circuit CDCAC. The real linear conflict remains the responsibility of the existing LRA sibling / TheoryManager path. An NRA-side linear fast path (short-circuit on linear-subset UNSAT) is a *separate* gated feature with its own differential validation, **not** part of this plan.

**Fresh-build, not sibling-reuse (master decision):** do **not** reuse the sibling `LraSolver`'s `GeneralSimplex` in Phase 1. Its lifecycle, active-literal set, polarity handling, check timing, and post-check tableau state are owned by `TheoryManager` and are not a stable contract for NRA variable ordering. Build a fresh `GeneralSimplex` from the active linear subset inside `SimplexTableauFacts` — self-contained, deterministic, independently unit-testable, and free of hidden coupling to solver-scheduling order. Reuse-the-sibling is a possible Phase-2 optimization once the state-sharing contract is explicit.

**Deferred to follow-up plans (NOT here):**
- Spec §6 Algorithm 5 (CDCAC prefix-level exact residual linear check → section/sector/refined cover) and §8–§11. This *changes verdicts* (an over-generalized cover is a false UNSAT) and needs `CdcacCore::solveLevel` surgery. It will reuse `SimplexTableauFacts` (which is why those facts are sound over-approximations, never tight, never used for pruning here). Its own plan + gate.
- True propagation / fixpoint implied-bound closure (Phase 2 of the facts module).
- Full bidirectional front/back placement (spec §5.2). Phase 1 implements front-variable selection only (Self-Review).

**Subsumed by existing architecture — deliberately NOT built:** spec P1 "Pure-LRA fast path" + "mixed-branch linear-subset UNSAT lemma". For `QF_NRA`/`QF_UFNRA`, `TheoryFactory::setupSolvers` (`src/frontend/factory/TheoryFactory.cpp:51-58`, `248-256`) registers an `LraSolver` **sibling** alongside `NraSolver`; `TheoryManager` drives both, so the linear atoms are already checked by a full incremental Simplex with conflict generation. **Task 0 is a hard gate verifying this — including the routing-split mixed-equality case.**

**Interaction with the existing `ZOLVER_NRA_VARORDER` (commit `18bd5e0`):** that flag (ascending total degree, highest-degree var projected first) is a *soundness mitigation* — an arbitrary order can place a high-degree variable at an outer lifting level and create close-irrational-root cells the covering mishandles (a latent CDCAC false-UNSAT bug). This plan **preserves** it: ascending total degree stays the primary sort key; `frontScore` only reorders variables sharing the same total-degree key (where degree-safety is non-discriminating, so it cannot be violated). The new mode lives behind its own flag so the validated degree-only baseline is unchanged.

**Soundness invariant for this plan:** Under an ideal, complete CDCAC without resource limits, variable order must not change the mathematical Sat/Unsat result. In *this* implementation the order is treated strictly as a heuristic that may affect timeout/Unknown behavior and may expose the known latent CDCAC ordering bug. Therefore: (a) the primary key stays ascending-total-degree (the existing mitigation); (b) the new flag is default-OFF; (c) it is not promotable until differential validation shows **zero** unsoundness (no flag-ON verdict contradicting the oracle) and acceptable performance. The only hard structural requirement is that the produced order is a permutation of exactly the variables in the constraints (Tasks 4 & 5 assert this). `SimplexTableauFacts` cannot affect soundness because it is heuristic-only and verdict-free.

---

## File Structure

```
src/theory/arith/nra/simplex/                 (NEW dir — auto-globbed by CONFIGURE_DEPENDS)
  NraLinearExtractor.h/.cpp     Classify CdcacConstraints linear vs nonlinear; extract (VarId,coeff)+const from linear ones.
  SimplexTableauFacts.h/.cpp    Fresh GeneralSimplex over the linear subset; on SAT read read-only solved-tableau facts. Facts-only.
  PolyStructureFacts.h/.cpp     Per-var nonlinearConnectivity, linearizationGain (residual-degree test), maxDegree.
  VarOrderSelector.h/.cpp       Degree-stratified order: primary = ascending total degree; tie-break = frontScore(facts).

src/theory/arith/nra/core/CdcacSolver.cpp     MODIFY: read ZOLVER_NRA_VARORDER_SIMPLEX; at the var-order site, when set, call computeCdcacVarOrder; existing ZOLVER_NRA_VARORDER and lexicographic paths untouched.
src/theory/arith/nra/core/CdcacSolver.h        MODIFY: add `bool simplexVarOrder_ = false;` member.

tests/unit/test_nra_simplex_varorder.cpp       NEW: unit tests for all four module pieces + the gated wiring.
```

Pipeline: `NraLinearExtractor` + `PolyStructureFacts` produce inputs; `SimplexTableauFacts` builds a fresh Simplex on the linear subset; `VarOrderSelector` fuses everything.

**Shared types (define in `NraLinearExtractor.h`, reused everywhere):**

```cpp
// src/theory/arith/nra/simplex/NraLinearExtractor.h
#pragma once
#include "expr/types.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include "theory/arith/nra/core/CdcacTypes.h" // CdcacConstraint, Relation, SatLit
#include <gmpxx.h>
#include <vector>

namespace zolver {

// One linear atom: (sum coeffs[i].second * coeffs[i].first) + constant  rel  0
struct LinearAtom {
    std::vector<std::pair<VarId, mpq_class>> coeffs; // degree-1 monomials
    mpq_class constant{0};                           // the powers-empty monomial
    Relation rel;
    SatLit reason;
};

struct ClassifiedConstraints {
    std::vector<LinearAtom> linear;          // every monomial has total degree <= 1
    std::vector<CdcacConstraint> nonlinear;  // at least one monomial of total degree >= 2
};

// Classify via kernel->terms(). A constraint whose terms() is nullopt
// (non-integer coeffs / unsupported) is treated as nonlinear (conservative).
ClassifiedConstraints classifyConstraints(
    const PolynomialKernel& kernel,
    const std::vector<CdcacConstraint>& constraints);

} // namespace zolver
```

> Confirm `CdcacConstraint`'s fields against `nra/core/CdcacTypes.h` during Task 1 (`CdcacSolver.cpp` uses `.poly`, `.rel`, `.reason`). `std::unordered_map<VarId,...>` needs a hash for `VarId`; `project_realvalue` added `std::hash` specializations — if `VarId` still lacks one, key on the underlying `uint32_t`. Verify, don't assume.

---

### Task 0: Confirm the LRA sibling resolves pure-linear / linear-subset / mixed-equality conflicts (HARD GATE)

**Files:** none modified — empirical verification justifying the scope boundary. If any expected verdict is wrong, **STOP** and report to the master: Phase 1 (ordering) does not fix routing soundness.

- [ ] **Step 1: Build the current solver (WSL-safe, bounded parallelism)**

Run:
```bash
cd build && ( ulimit -v 2000000; cmake --build . -j2 ) 2>&1 | tail -5
```
Expected: build succeeds, `bin/zolver` present.

- [ ] **Step 2: Write the probe battery**

`/tmp/p1_pure.smt2` (expect unsat):
```smt
(set-logic QF_NRA)
(declare-fun x () Real)
(assert (= x 0))
(assert (> x 0))
(check-sat)
```
`/tmp/p2_mixed_bounds.smt2` (expect unsat — purely from x≥1 ∧ x≤0):
```smt
(set-logic QF_NRA)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (= (* x y) 1))
(assert (>= x 1))
(assert (<= x 0))
(check-sat)
```
`/tmp/p3_eq_neg.smt2` (expect unsat):
```smt
(set-logic QF_NRA)
(declare-fun x () Real)
(assert (= x 0))
(assert (not (= x 0)))
(check-sat)
```
`/tmp/p4_distinct.smt2` (expect unsat):
```smt
(set-logic QF_NRA)
(declare-fun x () Real)
(assert (= x 0))
(assert (distinct x 0))
(check-sat)
```
`/tmp/p5_mixed_eq.smt2` (expect unsat — the routing-split case: a linear equality must reach CDCAC, not only the sibling):
```smt
(set-logic QF_NRA)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (= (* x y) 1))
(assert (= x 0))
(check-sat)
```

- [ ] **Step 3: Run all five**

Run:
```bash
for f in /tmp/p1_pure /tmp/p2_mixed_bounds /tmp/p3_eq_neg /tmp/p4_distinct /tmp/p5_mixed_eq; do
  echo -n "$f: "; ./build/bin/zolver solve "$f.smt2" 2>/dev/null | tail -1
done
```
Expected: **all five print `unsat`**.

- [ ] **Step 4: Decide**

All five `unsat` → scope boundary confirmed; proceed to Task 1.
Any other verdict (esp. `p5` returning `sat`/`unknown`, meaning a linear equality is consumed only by the sibling and never seen by CDCAC) → **STOP** and report the failing probe(s). This is routing soundness, which variable ordering cannot address.

---

### Task 1: Linear/nonlinear classification + linear-term extraction

**Files:**
- Create: `src/theory/arith/nra/simplex/NraLinearExtractor.h` (header above)
- Create: `src/theory/arith/nra/simplex/NraLinearExtractor.cpp`
- Test: `tests/unit/test_nra_simplex_varorder.cpp`

- [ ] **Step 1: Write the failing test**

Create `tests/unit/test_nra_simplex_varorder.cpp`:
```cpp
#include <doctest/doctest.h>
#include "theory/arith/nra/simplex/NraLinearExtractor.h"
#include "theory/arith/nra/core/CdcacTypes.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include <set>
#include <algorithm>

using namespace zolver;

static CdcacConstraint mkC(PolyId p, Relation r, int litVar) {
    CdcacConstraint c;
    c.poly = p; c.rel = r; c.reason = SatLit::positive(litVar);
    return c;
}

TEST_CASE("extractor: 2x + 3 >= 0 is linear with coeff 2 const 3") {
    auto kernel = createPolynomialKernel();
    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    PolyId two = kernel->mkConst(mpq_class(2));
    PolyId three = kernel->mkConst(mpq_class(3));
    PolyId p = kernel->add(kernel->mul(two, x), three);  // 2x + 3

    auto cc = classifyConstraints(*kernel, { mkC(p, Relation::Geq, 1) });
    REQUIRE(cc.linear.size() == 1);
    CHECK(cc.nonlinear.empty());
    const auto& la = cc.linear[0];
    REQUIRE(la.coeffs.size() == 1);
    CHECK(la.coeffs[0].first == kernel->getOrCreateVar("x"));
    CHECK(la.coeffs[0].second == mpq_class(2));
    CHECK(la.constant == mpq_class(3));
    CHECK(la.rel == Relation::Geq);
}

TEST_CASE("extractor: x*y - 1 is nonlinear") {
    auto kernel = createPolynomialKernel();
    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    PolyId y = kernel->mkVar(kernel->getOrCreateVar("y"));
    PolyId one = kernel->mkConst(mpq_class(1));
    PolyId p = kernel->sub(kernel->mul(x, y), one);  // x*y - 1

    auto cc = classifyConstraints(*kernel, { mkC(p, Relation::Eq, 1) });
    CHECK(cc.linear.empty());
    CHECK(cc.nonlinear.size() == 1);
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `( ulimit -v 2000000; cmake --build build -j2 ) 2>&1 | tail -20`
Expected: compile FAIL — `NraLinearExtractor.h: No such file`.

- [ ] **Step 3: Write minimal implementation**

Create `src/theory/arith/nra/simplex/NraLinearExtractor.cpp`:
```cpp
#include "theory/arith/nra/simplex/NraLinearExtractor.h"

namespace zolver {

ClassifiedConstraints classifyConstraints(
    const PolynomialKernel& kernel,
    const std::vector<CdcacConstraint>& constraints) {
    ClassifiedConstraints out;
    for (const auto& c : constraints) {
        auto termsOpt = kernel.terms(c.poly);
        if (!termsOpt) { out.nonlinear.push_back(c); continue; }  // conservative

        bool isLinear = true;
        for (const auto& t : *termsOpt) {
            int total = 0;
            for (const auto& pe : t.powers) total += pe.second;
            if (total >= 2) { isLinear = false; break; }
        }
        if (!isLinear) { out.nonlinear.push_back(c); continue; }

        LinearAtom la;
        la.rel = c.rel;
        la.reason = c.reason;
        for (const auto& t : *termsOpt) {
            if (t.powers.empty()) la.constant += mpq_class(t.coefficient);
            else la.coeffs.push_back({ t.powers[0].first, mpq_class(t.coefficient) });
        }
        out.linear.push_back(std::move(la));
    }
    return out;
}

} // namespace zolver
```

- [ ] **Step 4: Run test to verify it passes**

Run:
```bash
cd build && cmake .. >/dev/null && cd ..   # configure pass: pick up the new directory
( ulimit -v 2000000; cmake --build build -j2 ) && \
  ./build/tests/zolver_unit_tests --test-case="extractor*"
```
Expected: 2 cases PASS.

- [ ] **Step 5: Commit**

```bash
git add src/theory/arith/nra/simplex/NraLinearExtractor.h \
        src/theory/arith/nra/simplex/NraLinearExtractor.cpp \
        tests/unit/test_nra_simplex_varorder.cpp
git commit -m "feat(nra): linear/nonlinear constraint classifier + term extractor for cdcac varorder"
```

---

### Task 2: SimplexTableauFacts — fresh Simplex + read-only solved-tableau facts (facts-only)

**Files:**
- Create: `src/theory/arith/nra/simplex/SimplexTableauFacts.h`
- Create: `src/theory/arith/nra/simplex/SimplexTableauFacts.cpp`
- Test: `tests/unit/test_nra_simplex_varorder.cpp` (append)

> **One-shot solved-tableau observation, not a propagation engine** (see Scope for the exact must/must-not list). Build a *fresh* `GeneralSimplex`; on UNSAT return facts-only (`linearSubsetUnsat()`), never a conflict. The interval-derivation logic is factored into a pure helper `deriveBasicInterval` so it is tested independently of which variable the simplex happens to make basic. The tableau row convention (`xb = rhs + Σ coeff·col`) is pinned by a runtime identity test, not assumed.

- [ ] **Step 1: Write the failing tests**

Append:
```cpp
#include "theory/arith/nra/simplex/SimplexTableauFacts.h"
#include "theory/arith/lra/GeneralSimplex.h"
#include "theory/arith/lra/SparseTableau.h"

TEST_CASE("deriveBasicInterval: x = 1 - y over y in [0,1] -> [0,1]") {
    // xb = rhs + sum coeff*col ; here rhs=1, one term coeff=-1 with col bounds [0,1]
    std::vector<RowTermBound> terms = { RowTermBound{ mpq_class(-1), mpq_class(0), mpq_class(1) } };
    auto iv = deriveBasicInterval(mpq_class(1), terms);
    REQUIRE(iv.first.has_value());  CHECK(*iv.first  == mpq_class(0));
    REQUIRE(iv.second.has_value()); CHECK(*iv.second == mpq_class(1));
}

TEST_CASE("deriveBasicInterval: missing lower bound on a positive-coeff term drops lower side") {
    std::vector<RowTermBound> terms = { RowTermBound{ mpq_class(2), std::nullopt, mpq_class(5) } };
    auto iv = deriveBasicInterval(mpq_class(0), terms);
    CHECK(!iv.first.has_value());                   // lower needs col-lower (positive coeff) -> missing
    REQUIRE(iv.second.has_value()); CHECK(*iv.second == mpq_class(10));
}

TEST_CASE("tableau facts: x>=1 and x<=1 (single-var) -> fixed; bounded both sides") {
    auto kernel = createPolynomialKernel();
    VarId xv = kernel->getOrCreateVar("x");
    PolyId x = kernel->mkVar(xv);
    PolyId one = kernel->mkConst(mpq_class(1));
    PolyId xm1 = kernel->sub(x, one);
    auto cc = classifyConstraints(*kernel, {
        mkC(xm1, Relation::Geq, 1), mkC(xm1, Relation::Leq, 2) });
    SimplexTableauFacts f = computeSimplexTableauFacts(*kernel, cc.linear);
    CHECK(!f.linearSubsetUnsat());
    CHECK(f.hasLower(xv)); CHECK(f.hasUpper(xv)); CHECK(f.isFixed(xv));
}

TEST_CASE("tableau facts: x>=1 and x<=0 (single-var) -> linearSubsetUnsat, no facts, no conflict") {
    auto kernel = createPolynomialKernel();
    VarId xv = kernel->getOrCreateVar("x");
    PolyId x = kernel->mkVar(xv);
    PolyId one = kernel->mkConst(mpq_class(1));
    auto cc = classifyConstraints(*kernel, {
        mkC(kernel->sub(x, one), Relation::Geq, 1),   // x >= 1
        mkC(x,                   Relation::Leq, 2) }); // x <= 0
    SimplexTableauFacts f = computeSimplexTableauFacts(*kernel, cc.linear);
    CHECK(f.linearSubsetUnsat());
    CHECK(!f.hasLower(xv));  // no ordering facts on UNSAT
}

TEST_CASE("tableau row convention: value(basic) == rhs + sum coeff*value(col)") {
    // Build x + y = 1, 0<=y<=1, x<=5 ; solve; verify the affine row identity
    // that deriveBasicInterval relies on. Pins the sign convention empirically.
    GeneralSimplex gs;
    int xi = gs.addVar("x"), yi = gs.addVar("y");
    int s = gs.addConstraint({ {xi, mpq_class(1)}, {yi, mpq_class(1)} }, mpq_class(0)); // s = x+y
    gs.assertLower(s, BoundInfo(BoundValue(DeltaRational(mpq_class(1))), SatLit::positive(1)));
    gs.assertUpper(s, BoundInfo(BoundValue(DeltaRational(mpq_class(1))), SatLit::positive(1))); // x+y = 1
    gs.assertLower(yi, BoundInfo(BoundValue(DeltaRational(mpq_class(0))), SatLit::positive(2)));
    gs.assertUpper(yi, BoundInfo(BoundValue(DeltaRational(mpq_class(1))), SatLit::positive(3)));
    gs.assertUpper(xi, BoundInfo(BoundValue(DeltaRational(mpq_class(5))), SatLit::positive(4)));
    REQUIRE(gs.check() == GeneralSimplex::Result::Sat);
    for (int r = 0; r < gs.tableau().numRows(); ++r) {
        const SparseRow& row = gs.tableau().row(r);
        if (row.basicVar < 0) continue;
        DeltaRational lhs = gs.value(row.basicVar);
        mpq_class accA = row.rhs, accB = 0;
        for (const auto& e : row.entries) {
            DeltaRational cv = gs.value(e.col);
            accA += e.coeff * cv.a;
            accB += e.coeff * cv.b;
        }
        CHECK(lhs.a == accA);
        CHECK(lhs.b == accB);
    }
}

TEST_CASE("tableau facts: an ORIGINAL variable acquires a row-derived bound (end-to-end)") {
    // x + y = 1 ; y fixed at 1/4 ; x has NO direct single-variable bound.
    // y sits at its (only) bound and cannot move, so the simplex MUST pivot x into
    // the basis to satisfy s = x+y = 1. x's row then derives x purely from the
    // non-basic bounds (s, y) -> proves row-derived bounds reach the facts for an
    // original variable (not just the aux var). This is the headline behavior;
    // without it the module degrades to "stored bounds + participation".
    auto kernel = createPolynomialKernel();
    VarId xv = kernel->getOrCreateVar("x"), yv = kernel->getOrCreateVar("y");
    PolyId x = kernel->mkVar(xv), y = kernel->mkVar(yv);
    PolyId one = kernel->mkConst(mpq_class(1)), quarter = kernel->mkConst(mpq_class(1,4));
    auto cc = classifyConstraints(*kernel, {
        mkC(kernel->sub(kernel->add(x, y), one), Relation::Eq, 1),   // x + y - 1 = 0  (multi-var -> aux row)
        mkC(kernel->sub(y, quarter),             Relation::Eq, 2) });// y - 1/4 = 0    (single-var -> y fixed)
    SimplexTableauFacts f = computeSimplexTableauFacts(*kernel, cc.linear);
    REQUIRE(!f.linearSubsetUnsat());
    REQUIRE(f.isBasic(xv));            // construction forces x basic; if this fails, adjust the construction
    // x has NO direct bound atom, so these bounds can ONLY be row-derived:
    CHECK(f.hasLower(xv));
    CHECK(f.hasUpper(xv));
    CHECK(f.isFixed(xv));             // x = 1 - 1/4 = 3/4
}
```

> If `REQUIRE(f.isBasic(xv))` ever fails (a pivot rule leaves `x` non-basic), strengthen the construction so an original variable is provably basic (e.g. add a second fixed companion) — the test must assert a row-derived bound on an *original* variable, not merely that the helper math is correct.

- [ ] **Step 2: Run tests to verify they fail**

Run: `( ulimit -v 2000000; cmake --build build -j2 ) 2>&1 | tail -20`
Expected: FAIL — `SimplexTableauFacts.h: No such file`.

- [ ] **Step 3: Write the header**

Create `src/theory/arith/nra/simplex/SimplexTableauFacts.h`:
```cpp
#pragma once
#include "theory/arith/nra/simplex/NraLinearExtractor.h"
#include "expr/types.h"
#include <unordered_map>
#include <optional>
#include <utility>
#include <vector>
#include <gmpxx.h>

namespace zolver {

// One non-basic term of a basic variable's row, with that term variable's
// currently stored bounds (nullopt = unbounded on that side).
struct RowTermBound { mpq_class coeff; std::optional<mpq_class> lo, hi; };

// Pure interval arithmetic for one solved-tableau row: xb = rhs + Σ coeff·col.
// Returns (lower, upper); a side is nullopt if any required col bound is missing.
std::pair<std::optional<mpq_class>, std::optional<mpq_class>>
deriveBasicInterval(const mpq_class& rhs, const std::vector<RowTermBound>& terms);

// Read-only facts from a SOLVED (SAT) fresh GeneralSimplex over the linear
// subset. Heuristic input to CDCAC variable ordering ONLY — never used for
// pruning, conflicts, or verdicts. On UNSAT: linearSubsetUnsat() == true and
// no ordering facts are populated (no conflict is produced).
class SimplexTableauFacts {
public:
    bool linearSubsetUnsat() const { return unsat_; }

    bool hasLower(VarId v) const { auto it=m_.find(v); return it!=m_.end() && it->second.lo.has_value(); }
    bool hasUpper(VarId v) const { auto it=m_.find(v); return it!=m_.end() && it->second.hi.has_value(); }
    bool isFixed (VarId v) const { auto it=m_.find(v); return it!=m_.end() && it->second.lo && it->second.hi && *it->second.lo==*it->second.hi; }
    bool isBasic (VarId v) const { auto it=m_.find(v); return it!=m_.end() && it->second.basic; }
    int  boundedness(VarId v) const { return (hasLower(v)?1:0)+(hasUpper(v)?1:0); }
    int  rowParticipation(VarId v) const { return get(rowPart_, v); }
    int  tightRowParticipation(VarId v) const { return get(tight_, v); }

    struct E { std::optional<mpq_class> lo, hi; bool basic=false; };
    std::unordered_map<VarId,E>   m_;
    std::unordered_map<VarId,int> rowPart_, tight_;
    bool unsat_ = false;

    void tightenLower(VarId v, const mpq_class& b){ auto&e=m_[v]; if(!e.lo||b>*e.lo) e.lo=b; }
    void tightenUpper(VarId v, const mpq_class& b){ auto&e=m_[v]; if(!e.hi||b<*e.hi) e.hi=b; }
private:
    static int get(const std::unordered_map<VarId,int>&m, VarId v){ auto it=m.find(v); return it==m.end()?0:it->second; }
};

SimplexTableauFacts computeSimplexTableauFacts(
    const PolynomialKernel& kernel,
    const std::vector<LinearAtom>& linear);

} // namespace zolver
```

> Same `std::hash<VarId>` caveat as the shared-types note.

- [ ] **Step 4: Write the implementation**

Create `src/theory/arith/nra/simplex/SimplexTableauFacts.cpp`:
```cpp
#include "theory/arith/nra/simplex/SimplexTableauFacts.h"
#include "theory/arith/lra/GeneralSimplex.h"
#include "theory/arith/lra/DeltaRational.h"
#include "theory/arith/lra/SparseTableau.h"
#include <unordered_map>

namespace zolver {

std::pair<std::optional<mpq_class>, std::optional<mpq_class>>
deriveBasicInterval(const mpq_class& rhs, const std::vector<RowTermBound>& terms) {
    std::optional<mpq_class> lo = rhs, hi = rhs;
    for (const auto& t : terms) {
        if (t.coeff > 0) {            // lower uses col.lo, upper uses col.hi
            if (lo) { if (t.lo) *lo += t.coeff * *t.lo; else lo.reset(); }
            if (hi) { if (t.hi) *hi += t.coeff * *t.hi; else hi.reset(); }
        } else if (t.coeff < 0) {     // lower uses col.hi, upper uses col.lo
            if (lo) { if (t.hi) *lo += t.coeff * *t.hi; else lo.reset(); }
            if (hi) { if (t.lo) *hi += t.coeff * *t.lo; else hi.reset(); }
        }
    }
    return { lo, hi };
}

SimplexTableauFacts computeSimplexTableauFacts(
    const PolynomialKernel& kernel,
    const std::vector<LinearAtom>& linear) {
    SimplexTableauFacts F;
    GeneralSimplex gs;

    std::unordered_map<VarId,int> idx;    // kernel VarId -> simplex index
    std::unordered_map<int,VarId> orig;   // simplex index -> kernel VarId (originals only)
    auto idxOf = [&](VarId v)->int {
        auto it=idx.find(v); if (it!=idx.end()) return it->second;
        int i = gs.addVar(kernel.varName(v));
        idx[v]=i; orig[i]=v; return i;
    };
    auto flip = [](Relation r)->Relation {
        switch(r){ case Relation::Geq:return Relation::Leq; case Relation::Leq:return Relation::Geq;
                   case Relation::Gt:return Relation::Lt;   case Relation::Lt:return Relation::Gt;  default:return r; }
    };

    for (const auto& la : linear) {
        if (la.coeffs.empty()) {                   // constant atom: constant rel 0
            int s = (la.constant > 0) ? 1 : (la.constant < 0) ? -1 : 0;
            bool ok = true;
            switch (la.rel) {
                case Relation::Eq:  ok = (s == 0); break;
                case Relation::Neq: ok = (s != 0); break;
                case Relation::Lt:  ok = (s <  0); break;
                case Relation::Leq: ok = (s <= 0); break;
                case Relation::Gt:  ok = (s >  0); break;
                case Relation::Geq: ok = (s >= 0); break;
            }
            if (!ok) { F.unsat_ = true; return F; }   // false constant => linear subset infeasible
            continue;                                 // trivially-true constant: nothing to assert
        }
        if (la.rel == Relation::Neq) continue;     // non-convex (non-constant): skip
        if (la.coeffs.size() == 1) {               // a*x + c rel 0 -> direct bound on x
            VarId v = la.coeffs[0].first;
            const mpq_class& a = la.coeffs[0].second;
            if (a == 0) continue;
            mpq_class b = -la.constant / a;
            Relation rel = (a < 0) ? flip(la.rel) : la.rel;
            int xi = idxOf(v);
            switch (rel) {
                case Relation::Eq:  gs.assertLower(xi, BoundInfo(BoundValue(DeltaRational(b)), la.reason));
                                    gs.assertUpper(xi, BoundInfo(BoundValue(DeltaRational(b)), la.reason)); break;
                case Relation::Geq: gs.assertLower(xi, BoundInfo(BoundValue(DeltaRational(b)), la.reason)); break;
                case Relation::Gt:  gs.assertLower(xi, BoundInfo(BoundValue(DeltaRational(b, mpq_class(1))), la.reason)); break;
                case Relation::Leq: gs.assertUpper(xi, BoundInfo(BoundValue(DeltaRational(b)), la.reason)); break;
                case Relation::Lt:  gs.assertUpper(xi, BoundInfo(BoundValue(DeltaRational(b, mpq_class(-1))), la.reason)); break;
                default: break;
            }
        } else {                                   // multi-var -> aux row s = Σ a_j x_j ; bound s rel -const
            std::vector<std::pair<int,mpq_class>> terms;
            for (auto&[v,c] : la.coeffs) terms.push_back({ idxOf(v), c });
            int s = gs.addConstraint(terms, mpq_class(0));
            if (s < 0) continue;
            mpq_class rhs = -la.constant;
            switch (la.rel) {
                case Relation::Eq:  gs.assertLower(s, BoundInfo(BoundValue(DeltaRational(rhs)), la.reason));
                                    gs.assertUpper(s, BoundInfo(BoundValue(DeltaRational(rhs)), la.reason)); break;
                case Relation::Geq: gs.assertLower(s, BoundInfo(BoundValue(DeltaRational(rhs)), la.reason)); break;
                case Relation::Gt:  gs.assertLower(s, BoundInfo(BoundValue(DeltaRational(rhs, mpq_class(1))), la.reason)); break;
                case Relation::Leq: gs.assertUpper(s, BoundInfo(BoundValue(DeltaRational(rhs)), la.reason)); break;
                case Relation::Lt:  gs.assertUpper(s, BoundInfo(BoundValue(DeltaRational(rhs, mpq_class(-1))), la.reason)); break;
                default: break;
            }
        }
    }

    if (gs.check() != GeneralSimplex::Result::Sat) {
        F.unsat_ = true;            // facts-only: no conflict, no verdict
        return F;
    }

    auto storedLo = [&](int i)->std::optional<mpq_class>{
        auto vs=gs.varState(i); return vs.lower.bound.isFinite()?std::optional<mpq_class>(vs.lower.bound.value.a):std::nullopt; };
    auto storedHi = [&](int i)->std::optional<mpq_class>{
        auto vs=gs.varState(i); return vs.upper.bound.isFinite()?std::optional<mpq_class>(vs.upper.bound.value.a):std::nullopt; };

    // 1+2. stored bounds and one-shot derived intervals per ORIGINAL variable.
    for (auto& [v, i] : idx) {
        if (auto lo = storedLo(i)) F.tightenLower(v, *lo);
        if (auto hi = storedHi(i)) F.tightenUpper(v, *hi);
        bool basic = gs.isBasic(i);
        F.m_[v].basic = basic;
        if (basic) {
            const SparseRow& row = gs.tableau().row(gs.basicRowOfVar(i));
            std::vector<RowTermBound> terms;
            terms.reserve(row.entries.size());
            for (const auto& e : row.entries)
                terms.push_back(RowTermBound{ e.coeff, storedLo(e.col), storedHi(e.col) });
            auto iv = deriveBasicInterval(row.rhs, terms);
            if (iv.first)  F.tightenLower(v, *iv.first);
            if (iv.second) F.tightenUpper(v, *iv.second);
        }
    }

    // 3. row + tight-row participation (zero-slack: basic var currently at a bound).
    for (int r = 0; r < gs.tableau().numRows(); ++r) {
        const SparseRow& row = gs.tableau().row(r);
        int bv = row.basicVar;
        if (bv < 0) continue;
        auto vs = gs.varState(bv);
        DeltaRational val = gs.value(bv);
        bool tight = (vs.lower.bound.isFinite() && val == vs.lower.bound.value) ||
                     (vs.upper.bound.isFinite() && val == vs.upper.bound.value);
        auto bump = [&](int simIdx){ auto it=orig.find(simIdx); if(it!=orig.end()){ ++F.rowPart_[it->second]; if(tight) ++F.tight_[it->second]; } };
        bump(bv);
        for (const auto& e : row.entries) bump(e.col);
    }
    return F;
}

} // namespace zolver
```

> Verify against headers when implementing: `BoundInfo(BoundValue, SatLit)`, `BoundValue(DeltaRational)`, `DeltaRational(mpq)` / `DeltaRational(mpq,mpq)`, `varState(i).{lower,upper}.bound.{isFinite(),value.a}`, `value(i).{a,b}`, `isBasic`, `basicRowOfVar`, `tableau().row(r).{basicVar,rhs,entries}`, `RowEntry.{col,coeff}` — all present in `GeneralSimplex.h` / `SparseTableau.h` as of this writing. `lowSlackRowParticipation` is collapsed into `tightRowParticipation` (zero-slack) in Phase 1 — finer slack thresholds need a magic number and are deferred to weight-tuning.

- [ ] **Step 5: Run tests to verify they pass**

Run:
```bash
( ulimit -v 2000000; cmake --build build -j2 ) && \
  ./build/tests/zolver_unit_tests --test-case="deriveBasicInterval*" \
  --test-case="tableau facts*" --test-case="tableau row convention*"
```
Expected: all PASS. If "tableau row convention" FAILS, the row form is `xb − Σ coeff·col = rhs` (or similar) — flip the sign usage in `deriveBasicInterval`/the row read to match, then re-run. Do not "fix" by editing GeneralSimplex.

- [ ] **Step 6: Commit**

```bash
git add src/theory/arith/nra/simplex/SimplexTableauFacts.h \
        src/theory/arith/nra/simplex/SimplexTableauFacts.cpp \
        tests/unit/test_nra_simplex_varorder.cpp
git commit -m "feat(nra): SimplexTableauFacts — fresh-build LRA + read-only solved-tableau facts (facts-only)"
```

---

### Task 3: Polynomial structural facts (residual-degree linearization gain, connectivity, degree)

**Files:**
- Create: `src/theory/arith/nra/simplex/PolyStructureFacts.h`
- Create: `src/theory/arith/nra/simplex/PolyStructureFacts.cpp`
- Test: `tests/unit/test_nra_simplex_varorder.cpp` (append)

- [ ] **Step 1: Write the failing test**

Append:
```cpp
#include "theory/arith/nra/simplex/PolyStructureFacts.h"

TEST_CASE("structure: xy+xz-3 -> fixing x linearizes; fixing y/z does not") {
    auto kernel = createPolynomialKernel();
    VarId xv = kernel->getOrCreateVar("x"), yv = kernel->getOrCreateVar("y"), zv = kernel->getOrCreateVar("z");
    PolyId x = kernel->mkVar(xv), y = kernel->mkVar(yv), z = kernel->mkVar(zv);
    PolyId three = kernel->mkConst(mpq_class(3));
    PolyId p = kernel->sub(kernel->add(kernel->mul(x, y), kernel->mul(x, z)), three); // xy+xz-3
    CdcacConstraint c; c.poly = p; c.rel = Relation::Eq; c.reason = SatLit::positive(1);
    PolyStructureFacts f = computeStructureFacts(*kernel, { c });
    CHECK(f.linearizationGain(xv) == 1);
    CHECK(f.linearizationGain(yv) == 0);
    CHECK(f.linearizationGain(zv) == 0);
    CHECK(f.nonlinearConnectivity(xv) == 2);
    CHECK(f.nonlinearConnectivity(yv) == 1);
}

TEST_CASE("structure: xyz -> fixing any one variable does NOT linearize (residual degree 2)") {
    auto kernel = createPolynomialKernel();
    VarId xv = kernel->getOrCreateVar("x"), yv = kernel->getOrCreateVar("y"), zv = kernel->getOrCreateVar("z");
    PolyId x = kernel->mkVar(xv), y = kernel->mkVar(yv), z = kernel->mkVar(zv);
    PolyId p = kernel->mul(kernel->mul(x, y), z);   // x*y*z
    CdcacConstraint c; c.poly = p; c.rel = Relation::Eq; c.reason = SatLit::positive(1);
    PolyStructureFacts f = computeStructureFacts(*kernel, { c });
    CHECK(f.linearizationGain(xv) == 0);
    CHECK(f.linearizationGain(yv) == 0);
    CHECK(f.linearizationGain(zv) == 0);
}

TEST_CASE("structure: x*y^2 -> fixing y linearizes, fixing x does not") {
    auto kernel = createPolynomialKernel();
    VarId xv = kernel->getOrCreateVar("x"), yv = kernel->getOrCreateVar("y");
    PolyId x = kernel->mkVar(xv), y = kernel->mkVar(yv);
    PolyId p = kernel->mul(x, kernel->pow(y, 2));   // x*y^2
    CdcacConstraint c; c.poly = p; c.rel = Relation::Eq; c.reason = SatLit::positive(1);
    PolyStructureFacts f = computeStructureFacts(*kernel, { c });
    CHECK(f.linearizationGain(yv) == 1);
    CHECK(f.linearizationGain(xv) == 0);
    CHECK(f.maxDegree(yv) == 2);
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `( ulimit -v 2000000; cmake --build build -j2 ) 2>&1 | tail -20`
Expected: FAIL — `PolyStructureFacts.h: No such file`.

- [ ] **Step 3: Write the header**

Create `src/theory/arith/nra/simplex/PolyStructureFacts.h`:
```cpp
#pragma once
#include "theory/arith/poly/PolynomialKernel.h"
#include "theory/arith/nra/core/CdcacTypes.h"
#include "expr/types.h"
#include <unordered_map>
#include <vector>

namespace zolver {

class PolyStructureFacts {
public:
    int linearizationGain(VarId v) const { return get(linGain_, v); }
    int nonlinearConnectivity(VarId v) const { return get(connect_, v); }
    int maxDegree(VarId v) const { return get(maxDeg_, v); }

    std::unordered_map<VarId,int> linGain_, connect_, maxDeg_;
private:
    static int get(const std::unordered_map<VarId,int>& m, VarId v) {
        auto it = m.find(v); return it == m.end() ? 0 : it->second;
    }
};

PolyStructureFacts computeStructureFacts(
    const PolynomialKernel& kernel,
    const std::vector<CdcacConstraint>& nonlinearConstraints);

} // namespace zolver
```

- [ ] **Step 4: Write the implementation**

Create `src/theory/arith/nra/simplex/PolyStructureFacts.cpp`:
```cpp
#include "theory/arith/nra/simplex/PolyStructureFacts.h"
#include <set>

namespace zolver {

namespace {
// A monomial of total degree d with v-exponent e becomes linear after fixing v
// iff d <= 1 (already linear) or (v present and d - e <= 1).
bool monomialLinearAfterFixing(const PolynomialKernel::MonomialTerm& t, VarId v) {
    int total = 0, ev = 0;
    for (const auto& pe : t.powers) { total += pe.second; if (pe.first == v) ev = pe.second; }
    if (total <= 1) return true;
    if (ev == 0) return false;
    return (total - ev) <= 1;
}
} // namespace

PolyStructureFacts computeStructureFacts(
    const PolynomialKernel& kernel,
    const std::vector<CdcacConstraint>& nonlinearConstraints) {
    PolyStructureFacts f;
    for (const auto& c : nonlinearConstraints) {
        auto termsOpt = kernel.terms(c.poly);
        if (!termsOpt) continue;

        bool hasNonlinearMon = false;
        std::set<VarId> varsInC;
        for (const auto& t : *termsOpt) {
            int total = 0;
            for (const auto& pe : t.powers) total += pe.second;
            bool nl = (total >= 2);
            if (nl) hasNonlinearMon = true;
            for (const auto& pe : t.powers) {
                VarId v = pe.first;
                varsInC.insert(v);
                if (pe.second > f.maxDeg_[v]) f.maxDeg_[v] = pe.second;
                if (nl) ++f.connect_[v];
            }
        }
        if (!hasNonlinearMon) continue;

        for (VarId v : varsInC) {
            bool all = true;
            for (const auto& t : *termsOpt)
                if (!monomialLinearAfterFixing(t, v)) { all = false; break; }
            if (all) ++f.linGain_[v];
        }
    }
    return f;
}

} // namespace zolver
```

> If `MonomialTerm` is not nested as `PolynomialKernel::MonomialTerm`, match `PolynomialKernel.h:190`.

- [ ] **Step 5: Run tests to verify they pass**

Run:
```bash
( ulimit -v 2000000; cmake --build build -j2 ) && \
  ./build/tests/zolver_unit_tests --test-case="structure:*"
```
Expected: 3 cases PASS.

- [ ] **Step 6: Commit**

```bash
git add src/theory/arith/nra/simplex/PolyStructureFacts.h \
        src/theory/arith/nra/simplex/PolyStructureFacts.cpp \
        tests/unit/test_nra_simplex_varorder.cpp
git commit -m "feat(nra): polynomial structural facts with residual-degree linearization gain"
```

---

### Task 4: Degree-stratified variable-order selector

**Files:**
- Create: `src/theory/arith/nra/simplex/VarOrderSelector.h`
- Create: `src/theory/arith/nra/simplex/VarOrderSelector.cpp`
- Test: `tests/unit/test_nra_simplex_varorder.cpp` (append)

> Primary sort key = ascending total-degree sum (identical to `ZOLVER_NRA_VARORDER`; highest-degree var LAST = projected first; preserves the soundness mitigation). `frontScore` only orders variables sharing the same total-degree key — within a stratum, degree-safety is non-discriminating, so this tie-break has **no soundness effect**. Higher `frontScore` is placed *later* in `varOrder` (projected earlier), matching the spec intent that linearizing variables are decomposed first. Weights: `linearizationGain` dominates; tableau/bound facts are weak tie-breaks and must not outrank it.

- [ ] **Step 1: Write the failing test**

Append:
```cpp
#include "theory/arith/nra/simplex/VarOrderSelector.h"

static int posOf(const std::vector<std::string>& v, const std::string& n) {
    return (int)(std::find(v.begin(), v.end(), n) - v.begin());
}

TEST_CASE("varorder: highest total degree goes last (projected first)") {
    auto kernel = createPolynomialKernel();
    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    PolyId y = kernel->mkVar(kernel->getOrCreateVar("y"));
    PolyId z = kernel->mkVar(kernel->getOrCreateVar("z"));
    PolyId three = kernel->mkConst(mpq_class(3)), two = kernel->mkConst(mpq_class(2));
    PolyId core = kernel->sub(kernel->add(kernel->mul(x, y), kernel->mul(x, z)), three);
    PolyId ym2 = kernel->sub(y, two), zm2 = kernel->sub(z, two);
    PolyId xmHalf = kernel->sub(x, kernel->mkConst(mpq_class(1,2)));
    auto C = [](PolyId p, Relation r, int l){ CdcacConstraint c; c.poly=p; c.rel=r; c.reason=SatLit::positive(l); return c; };
    std::vector<CdcacConstraint> cons = {
        C(core, Relation::Eq, 1), C(ym2, Relation::Geq, 2),
        C(zm2, Relation::Geq, 3), C(xmHalf, Relation::Leq, 4) };
    std::vector<std::string> names = {"x", "y", "z"};
    auto order = computeCdcacVarOrder(*kernel, cons, names);
    REQUIRE(order.size() == 3);
    CHECK(order.back() == "x");                               // x has the highest degSum
    std::set<std::string> got(order.begin(), order.end());
    CHECK(got == std::set<std::string>{"x", "y", "z"});
}

TEST_CASE("varorder: within equal degree, higher linearization-gain var is later") {
    auto kernel = createPolynomialKernel();
    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    PolyId y = kernel->mkVar(kernel->getOrCreateVar("y"));
    PolyId a = kernel->mkVar(kernel->getOrCreateVar("a"));
    PolyId b = kernel->mkVar(kernel->getOrCreateVar("b"));
    PolyId one = kernel->mkConst(mpq_class(1));
    PolyId c1 = kernel->sub(kernel->mul(a, x), one);                       // a*x - 1  (fixing a linearizes)
    PolyId c2 = kernel->sub(kernel->mul(kernel->mul(b, x), y), one);       // b*x*y - 1 (fixing b leaves x*y)
    auto C = [](PolyId p, Relation r, int l){ CdcacConstraint c; c.poly=p; c.rel=r; c.reason=SatLit::positive(l); return c; };
    std::vector<CdcacConstraint> cons = { C(c1, Relation::Eq, 1), C(c2, Relation::Eq, 2) };
    std::vector<std::string> names = {"a", "b", "x", "y"};                  // a,b,y degSum 1; x degSum 2
    auto order = computeCdcacVarOrder(*kernel, cons, names);
    CHECK(order.back() == "x");                                            // highest degree last
    CHECK(posOf(order, "a") > posOf(order, "b"));                          // a linearizes -> later than b
    std::set<std::string> got(order.begin(), order.end());
    CHECK(got == std::set<std::string>{"a","b","x","y"});
}

TEST_CASE("varorder: all-linear input is a valid deterministic permutation") {
    auto kernel = createPolynomialKernel();
    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    PolyId y = kernel->mkVar(kernel->getOrCreateVar("y"));
    auto C = [](PolyId p, Relation r, int l){ CdcacConstraint c; c.poly=p; c.rel=r; c.reason=SatLit::positive(l); return c; };
    std::vector<CdcacConstraint> cons = { C(x, Relation::Geq, 1), C(y, Relation::Leq, 2) };
    std::vector<std::string> names = {"x", "y"};
    auto order = computeCdcacVarOrder(*kernel, cons, names);
    std::set<std::string> got(order.begin(), order.end());
    CHECK(got == std::set<std::string>{"x", "y"});
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `( ulimit -v 2000000; cmake --build build -j2 ) 2>&1 | tail -20`
Expected: FAIL — `VarOrderSelector.h: No such file`.

- [ ] **Step 3: Write the header**

Create `src/theory/arith/nra/simplex/VarOrderSelector.h`:
```cpp
#pragma once
#include "theory/arith/poly/PolynomialKernel.h"
#include "theory/arith/nra/core/CdcacTypes.h"
#include <string>
#include <vector>

namespace zolver {

// Degree-stratified CDCAC variable order. Primary key: ascending total-degree
// sum (highest-degree var LAST). Tie-break within a stratum: descending
// frontScore (linearizing/connected/tableau-bounded vars placed later). Final
// tie-break: original position. Returns a permutation of exactly `varNames`.
std::vector<std::string> computeCdcacVarOrder(
    const PolynomialKernel& kernel,
    const std::vector<CdcacConstraint>& constraints,
    const std::vector<std::string>& varNames);

} // namespace zolver
```

- [ ] **Step 4: Write the implementation**

Create `src/theory/arith/nra/simplex/VarOrderSelector.cpp`:
```cpp
#include "theory/arith/nra/simplex/VarOrderSelector.h"
#include "theory/arith/nra/simplex/NraLinearExtractor.h"
#include "theory/arith/nra/simplex/SimplexTableauFacts.h"
#include "theory/arith/nra/simplex/PolyStructureFacts.h"
#include <algorithm>
#include <optional>
#include <unordered_map>

namespace zolver {

std::vector<std::string> computeCdcacVarOrder(
    const PolynomialKernel& kernel,
    const std::vector<CdcacConstraint>& constraints,
    const std::vector<std::string>& varNames) {
    auto cc = classifyConstraints(kernel, constraints);
    SimplexTableauFacts tf = computeSimplexTableauFacts(kernel, cc.linear);
    PolyStructureFacts  sf = computeStructureFacts(kernel, cc.nonlinear);

    // Primary key: total-degree sum per variable (same as ZOLVER_NRA_VARORDER).
    std::unordered_map<std::string, int> degSum;
    for (const auto& name : varNames) degSum[name] = 0;
    for (const auto& c : constraints)
        for (const auto& name : varNames)
            if (auto d = kernel.degree(c.poly, name)) degSum[name] += *d;

    struct Scored { std::string name; int origPos; int deg; double front; };
    std::vector<Scored> v;
    v.reserve(varNames.size());
    for (size_t i = 0; i < varNames.size(); ++i) {
        // Look up the EXISTING VarId (const-correct: getOrCreateVar is non-const,
        // and ordering must never mint new variables). Names come from the active
        // constraints, so findVar succeeds; a miss => neutral frontScore.
        std::optional<VarId> idOpt = kernel.findVar(varNames[i]);
        if (!idOpt) { v.push_back({ varNames[i], (int)i, degSum[varNames[i]], 0.0 }); continue; }
        VarId id = *idOpt;
        // frontScore: structural linearization dominates; tableau facts are weak
        // tie-breaks (heuristic-only; never affect soundness).
        double front =
              3.0  * sf.linearizationGain(id)
            + 1.0  * sf.nonlinearConnectivity(id)
            + 0.5  * (tf.isFixed(id) ? 1 : 0)
            + 0.5  * tf.tightRowParticipation(id)
            + 0.25 * tf.boundedness(id)
            + 0.25 * (tf.isBasic(id) ? 1 : 0)
            - 1.0  * std::max(0, sf.maxDegree(id) - 1);   // algebraicComplexityPenalty
        v.push_back({ varNames[i], (int)i, degSum[varNames[i]], front });
    }
    // Ascending degree; within equal degree, ascending frontScore (higher
    // frontScore => later); final tie-break original position.
    std::stable_sort(v.begin(), v.end(), [](const Scored& a, const Scored& b) {
        if (a.deg != b.deg)     return a.deg   < b.deg;
        if (a.front != b.front) return a.front < b.front;
        return a.origPos < b.origPos;
    });
    std::vector<std::string> out;
    out.reserve(v.size());
    for (const auto& s : v) out.push_back(s.name);
    return out;
}

} // namespace zolver
```

- [ ] **Step 5: Run tests to verify they pass**

Run:
```bash
( ulimit -v 2000000; cmake --build build -j2 ) && \
  ./build/tests/zolver_unit_tests --test-case="varorder:*"
```
Expected: 3 cases PASS — `x` last in the first two; `a` later than `b`; valid permutations.

- [ ] **Step 6: Commit**

```bash
git add src/theory/arith/nra/simplex/VarOrderSelector.h \
        src/theory/arith/nra/simplex/VarOrderSelector.cpp \
        tests/unit/test_nra_simplex_varorder.cpp
git commit -m "feat(nra): degree-stratified cdcac variable-order selector (frontScore tie-break)"
```

---

### Task 5: Wire selector into CdcacSolver behind ZOLVER_NRA_VARORDER_SIMPLEX (default OFF)

**Files:**
- Modify: `src/theory/arith/nra/core/CdcacSolver.h` (add member)
- Modify: `src/theory/arith/nra/core/CdcacSolver.cpp` (var-order site `~141-167` + ctor + includes)
- Test: `tests/unit/test_nra_simplex_varorder.cpp` (append)

> Read the current a2 site first: a lexicographic `std::sort(varOrderNames...)` base, then a `static const bool kDegreeVarOrder = std::getenv("ZOLVER_NRA_VARORDER") != nullptr;` block that degree-sorts, then the `getOrCreateVar` loop. Add a *third* branch that supersedes the degree-only branch when the new flag is set; leave the existing degree-only branch and the OFF path byte-identical.

- [ ] **Step 1: Write the smoke test (verdict identical on/off)**

Append:
```cpp
#include "theory/arith/nra/core/CdcacSolver.h"
#include <cstdlib>

TEST_CASE("cdcac varorder flag: same verdict on/off for xy + x^2 - 2 = 0 ∧ y>=1") {
    auto run = [](bool on) {
        if (on) setenv("ZOLVER_NRA_VARORDER_SIMPLEX", "1", 1);
        else    unsetenv("ZOLVER_NRA_VARORDER_SIMPLEX");
        auto kernel = createPolynomialKernel();
        CdcacSolver solver(kernel.get());
        PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
        PolyId y = kernel->mkVar(kernel->getOrCreateVar("y"));
        PolyId one = kernel->mkConst(mpq_class(1)), two = kernel->mkConst(mpq_class(2));
        PolyId core = kernel->sub(kernel->add(kernel->mul(x, y), kernel->pow(x, 2)), two);
        PolyId ym1 = kernel->sub(y, one);
        solver.assertConstraint(core, Relation::Eq,  SatLit::positive(1), 0);
        solver.assertConstraint(ym1,  Relation::Geq, SatLit::positive(2), 0);
        auto r = solver.check(CdcacEffort::Full, nullptr);
        return r.kind;
    };
    auto off = run(false);
    auto on  = run(true);
    unsetenv("ZOLVER_NRA_VARORDER_SIMPLEX");
    CHECK(off == on);   // order must not change the verdict on a decidable case
}
```

- [ ] **Step 2: Build (test passes trivially until wiring exists)**

Run: `( ulimit -v 2000000; cmake --build build -j2 ) 2>&1 | tail -20`
Expected: compiles; test likely PASS already (both runs use the OFF path). Real verification is Step 4 + Task 6. If it FAILS once wiring lands, the selector changed a verdict on a decidable case — STOP, debug per `superpowers:systematic-debugging`.

- [ ] **Step 3: Implement the wiring**

In `CdcacSolver.h`, add a private bool member near other flags:
```cpp
    bool simplexVarOrder_ = false;   // ZOLVER_NRA_VARORDER_SIMPLEX
```

In `CdcacSolver.cpp`, add includes near the top:
```cpp
#include "theory/arith/nra/simplex/VarOrderSelector.h"
#include <cstdlib>
```

Initialize the flag once in every `CdcacSolver` constructor body:
```cpp
    if (const char* e = std::getenv("ZOLVER_NRA_VARORDER_SIMPLEX"))
        simplexVarOrder_ = (e[0]=='1'||e[0]=='t'||e[0]=='T'||e[0]=='y'||e[0]=='Y');
```

At the var-order site, after the lexicographic base, guard the existing degree block so the two flags don't both fire:
```cpp
    // Base: lexicographic (deterministic).
    std::sort(varOrderNames.begin(), varOrderNames.end());

    if (simplexVarOrder_ && varOrderNames.size() > 1) {
        // Degree-stratified order + frontScore tie-break (supersedes degree-only).
        varOrderNames = computeCdcacVarOrder(*kernel_, input.constraints, varOrderNames);
    } else {
        // Existing ZOLVER_NRA_VARORDER: degree-only ordering (unchanged).
        static const bool kDegreeVarOrder = std::getenv("ZOLVER_NRA_VARORDER") != nullptr;
        if (kDegreeVarOrder && varOrderNames.size() > 1) {
            std::unordered_map<std::string, int> degSum;
            for (const auto& name : varOrderNames) degSum[name] = 0;
            for (const auto& c : active_)
                for (const auto& name : varOrderNames)
                    if (auto d = kernel_->degree(c.poly, name)) degSum[name] += *d;
            std::stable_sort(varOrderNames.begin(), varOrderNames.end(),
                [&degSum](const std::string& a, const std::string& b) { return degSum[a] < degSum[b]; });
        }
    }
    for (const auto& name : varOrderNames) {
        input.varOrder.push_back(kernel_->getOrCreateVar(name));
    }
```

> Match the surrounding code exactly when you read the file — only move the existing degree block into the `else` branch; do not change its behavior when the new flag is unset.

- [ ] **Step 4: Build and run the new test + the existing CDCAC suite**

Run:
```bash
( ulimit -v 2000000; cmake --build build -j2 ) && \
  ./build/tests/zolver_unit_tests --test-case="cdcac varorder flag*" && \
  ./build/tests/zolver_unit_tests --test-case="CDCAC*"
```
Expected: new test PASS; all existing `CDCAC*` cases PASS (flag OFF by default → unchanged).

- [ ] **Step 5: Commit**

```bash
git add src/theory/arith/nra/core/CdcacSolver.h \
        src/theory/arith/nra/core/CdcacSolver.cpp \
        tests/unit/test_nra_simplex_varorder.cpp
git commit -m "feat(nra): gate degree-stratified cdcac varorder behind ZOLVER_NRA_VARORDER_SIMPLEX (default off)"
```

---

### Task 6: Full validation + promotion gate

**Files:** none modified — verification only (per `superpowers:verification-before-completion`).

- [ ] **Step 1: Full unit suite (flag OFF — default)**

Run:
```bash
( ulimit -v 2000000; ./build/tests/zolver_unit_tests ) 2>&1 | tail -5
```
Expected: all cases pass (a2 baseline 706 + the new cases). Record the exact count.

- [ ] **Step 2: Regression OFF (must match the a2 baseline exactly)**

Run:
```bash
( ulimit -v 2000000; python3 tools/run_regression.py --root tests/regression \
    --solver build/bin/zolver --timeout 20 -j 2 ) 2>&1 | tail -15
```
Expected: 633/633 (a2 baseline), 0 KNOWN_FAIL, 0 UNSOUND.

- [ ] **Step 3: Regression ON (soundness floor — no contradiction with oracle)**

Run:
```bash
( ulimit -v 2000000; ZOLVER_NRA_VARORDER_SIMPLEX=1 python3 tools/run_regression.py --root tests/regression \
    --solver build/bin/zolver --timeout 20 -j 2 ) 2>&1 | tail -15
```
Mandatory: **0 UNSOUND**. Variable ordering ON may *improve or degrade* timeout/Unknown behavior — verdict count can go up or down. Record recovered cases (Unknown/timeout → decided) and regressed cases (decided → Unknown/timeout) **separately**. Any flag-ON verdict that contradicts the oracle (e.g. a flip to UNSAT where z3 says SAT — the latent CDCAC ordering bug) is a **hard stop**.

- [ ] **Step 4: Differential check on the NRA bucket vs z3**

Run:
```bash
for f in tests/regression/nra/*.smt2; do
  off=$( ( ulimit -v 2000000; timeout 20 ./build/bin/zolver solve "$f" ) 2>/dev/null | tail -1 )
  on=$(  ( ulimit -v 2000000; timeout 20 env ZOLVER_NRA_VARORDER_SIMPLEX=1 ./build/bin/zolver solve "$f" ) 2>/dev/null | tail -1 )
  if [ "$off" != "$on" ]; then
    z3v=$( timeout 20 z3 "$f" 2>/dev/null | tail -1 )
    echo "$f  OFF=$off  ON=$on  Z3=$z3v"
  fi
done
```
Expected: for every differing line, `ON` agrees with `Z3` (recovery) and never contradicts `Z3` (would be unsound — STOP). Lines where OFF was `unknown`/timeout and `ON == Z3` are the wins this plan targets.

- [ ] **Step 5: Record results and the promotion decision**

Append a short results block (counts OFF vs ON, # recovered, # regressed, explicit 0-unsound confirmation). Promotion to default-ON (per `feedback_final_all_optimizations_on` + `feedback_floor_vs_recovery`) requires: **0 unsound**, **no oracle contradiction**, **net recovery**, and **no unacceptable timeout regression** on the full corpus. If ON merely floors (no net recovery), keep it default-OFF and report the residual as the next target (likely the deferred P3 residual-cover, which will reuse `SimplexTableauFacts`).

- [ ] **Step 6: Commit the results block**

```bash
git add docs/superpowers/plans/2026-05-27-simplex-enhanced-cdcac-varorder.md
git commit -m "docs(nra): record cdcac varorder validation results + promotion decision"
```

---

## Self-Review

**Spec coverage:**
- Spec §1 routing (classify active atoms linear vs nonlinear): Task 1.
- Spec §2 Alg 2 + §3 Alg 3 steps 4–6 (pure-LRA / linear-subset lemma): subsumed by the LRA sibling; Task 0 hard-gate verifies it, incl. the routing-split mixed-equality case.
- Spec §4 SimplexFacts: the cheap, exact, *one-shot* subset — structural facts (Task 3) + solved-tableau facts (Task 2: stored bounds, basic-row-derived intervals, fixedness, basis/row/tight participation, model value). Iterative implied-bound closure / per-variable LP / tight-row *slack thresholds* are deferred. Facts are sound over-approximations (interval arithmetic), never tight, never used for pruning — which also makes them safe to reuse in the deferred P3.
- Spec §5 frontScore + §5.3 Alg 4 (variable order): Tasks 3+4, degree-stratified — frontScore is a *within-stratum tie-break*, not a free sort (preserves the `18bd5e0` mitigation).
- Spec §5.2 back-variable placement: **not implemented**. Phase 1 is front-variable selection only; tableau boundedness/basis are *weak* tie-breaks (weights ≤ 0.25/0.5, below `linearizationGain` weight 3.0), explicitly not full fiber scheduling.
- Spec §6 Alg 5 + §8–§11 (residual → cover): deferred to the P3 follow-up plan (changes verdicts).

**Facts-only / fresh-build (master decisions):** Task 2 builds a *fresh* `GeneralSimplex` (no sibling reuse — Scope), and on UNSAT returns `linearSubsetUnsat()` with no facts and **no conflict / no short-circuit** (Scope). It never emits a SAT-level lemma and never participates in pruning or the verdict — verified by the UNSAT test (Task 2 Step 1) and the on/off verdict-equivalence test (Task 5 Step 1).

**Not propagation:** `SimplexTableauFacts` does one pass over the solved tableau (`deriveBasicInterval` per basic var) — no fixpoint, no chaining derived bounds into other rows, no reverse inference, no per-variable LP. The tableau already encodes one round of substitution; we only observe it.

**Disequality handling:** `Neq` atoms are skipped when building the Simplex (non-convex). May lose bound/fixedness info; cannot affect correctness.

**Soundness wording:** the Scope invariant does not claim order is verdict-invariant in this implementation; Task 6 does not claim monotone verdict count — it records recovered/regressed separately and treats any oracle contradiction as a hard stop.

**Placeholder scan:** every code step has complete code; commands have expected output. Flagged confirmations (`VarId` hash; `CdcacConstraint` fields; `MonomialTerm` nesting; row affine convention via the identity test; exact a2 var-order site text) are explicit verify-don't-assume instructions with fallbacks.

**Type consistency:** `LinearAtom`/`ClassifiedConstraints` (Task 1) feed Tasks 2 & 4. `RowTermBound`/`deriveBasicInterval` (Task 2) used by its own impl + tested directly. Accessors `hasLower/hasUpper/isFixed/isBasic/boundedness/tightRowParticipation` (Task 2) and `linearizationGain/nonlinearConnectivity/maxDegree` (Task 3) match their uses in Task 4's `computeCdcacVarOrder`, whose signature matches the Task 5 call. Flag `ZOLVER_NRA_VARORDER_SIMPLEX` identical in Tasks 5 & 6.

**Risk note:** the only soundness-relevant edit is Task 5's added var-order branch. The primary key stays ascending-total-degree, so the new mode cannot relax the degree-safety mitigation; within-stratum reordering is heuristic and `SimplexTableauFacts` is verdict-free. Residual risk (a within-stratum order exposing the latent CDCAC bug) is contained by default-OFF + the Task 6 hard oracle gate. No verdict-bearing CDCAC code is touched.
```
