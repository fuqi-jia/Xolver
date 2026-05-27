# NRA lever-2: FlatMonomialMap<V> — replace RationalPolynomial's std::map<heap-vector,mpq>

> **For agentic workers:** REQUIRED SUB-SKILL: superpowers:subagent-driven-development. Checkbox (`- [ ]`) tracking.

**Goal:** Replace `RationalPolynomial`'s `std::map<MonomialKey, mpq_class>` (RB-tree node + heap key-vector per term + node-by-node deep copy) with a flat, move-cheap, allocation-light `FlatMonomialMap<V>` (sorted `std::vector<std::pair<SmallVector key, V>>`). Verdict-preserving (canonical sorted/zero-stripped form preserved). Cuts the NRA projection/lifting allocation churn — the hong/hycomp timeouts and the hycomp `bad_alloc` OOM.

**Architecture:** New reusable templated utility `FlatMonomialMap<V>` with a `std::map`-compatible-enough surface (begin/end sorted, `find`, `rbegin`/`back`, `front`, `at`, `operator[]`, `operator==`, size/empty/clear) backed by a sorted vector, plus an `append` + `canonicalize()` fast build path. `MonomialKey` becomes `SmallVector<std::pair<VarId,int>, 4>` (inline small monomials → no per-key heap alloc). `RationalPolynomial::terms_` becomes `FlatMonomialMap<mpq_class>`; `terms()` returns it by const-ref. This round wires it into `RationalPolynomial` ONLY — `PolyBitBlaster::magCache_` (A6/bit-blast, same shape) is a deferred drop-in for the integrated bit-blast, NOT touched here.

**Tech Stack:** C++17, `SmallVector` (`src/util/`), GMP (`mpq_class`), libpoly (unaffected), doctest, SMT-LIB2 regression vs z3.

---

## Soundness model
This is an **ungated default-path refactor** (no flag — you can't cheaply keep two representations). It is verdict-preserving **by construction**: `FlatMonomialMap` maintains the exact canonical form `std::map` did (keys sorted ascending, unique, zero-coefficient entries stripped), so every consumer sees byte-identical terms in identical order. **Prove it empirically:** capture the pre-refactor baseline FIRST (Task 0), then require post-refactor full-regression verdicts identical (0 change, 0 unsound) and the projection/lifting unit groups unchanged. The 6 map-dependent consumer sites + `SmallVector` `operator==`/`<` are the entire code surface (mapped in the blast-radius survey).

**Canonical-form invariant (must hold after `canonicalize()`/`normalize()`):** entries sorted strictly-ascending by key (lex on `(VarId, exp)`), no duplicate keys, no zero-`V` entries, empty key = constant term sorts first. Any deviation is a verdict risk — Task 1 unit-tests this directly; Task 4 proves it end-to-end.

---

## File Structure
```
src/util/SmallVector.h                              MODIFY: add operator== and operator< (lexicographic) — needed for monomial keys.
src/theory/arith/poly/FlatMonomialMap.h             NEW: templated flat sorted-vector monomial map (header-only).
src/theory/arith/poly/RationalPolynomial.{h,cpp}    MODIFY: MonomialKey -> SmallVector alias; terms_ -> FlatMonomialMap<mpq_class>; terms() return type; adapt mutators/ops (append+canonicalize on hot build; normalize() canonicalizes).
src/theory/arith/{presolve,nra/projection}/...      MODIFY (6 sites): adapt the map-dependent calls (.find/.rbegin()->second/.begin()->second/.at) to FlatMonomialMap's surface.
tests/unit/test_flat_monomial_map.cpp               NEW: FlatMonomialMap unit tests.
```

---

### Task 0: Capture the pre-refactor baseline (the gate's reference) — DO FIRST

**Files:** none (measurement). This must run on the CURRENT tree before any edit.

- [ ] **Step 1:** Build current tree: `cd /mnt/d/D_Study/BUAA/projects/zolver-a2 && ( ulimit -v 4000000; cmake --build build -j2 ) 2>&1 | tail -3`.
- [ ] **Step 2:** Full regression, save per-case verdicts to a baseline file:
  `( ulimit -v 4000000; python3 tools/run_regression.py --root tests/regression --solver build/bin/zolver --timeout 20 -j 2 ) 2>&1 | tee /tmp/baseline_regression.txt | tail -8`. Record pass/total + UNSOUND. (If run_regression has a per-case output mode/flag, capture per-case verdicts; else capture the summary + KNOWN_FAILURES state.)
- [ ] **Step 3:** Perf sentinels — record DEFAULT-path time/verdict (no flags) for each, 25s timeout:
  `nra_124` = `tests/regression/nra/nra_124_sat_robotic_workspace.smt2`; `kissing_2_2/2_3/2_4` and `hong_5/6/7` under `/mnt/d/D_Study/BUAA/projects/NLColver/benchmark/non-incremental/QF_NRA/{kissing,hong}/`; the OOM case `hycomp/ball_count_1d_plain.01.qfree_global_10.smt2`. For each: `s=$(date +%s.%N); ( ulimit -v 4000000; timeout 25 ./build/bin/zolver solve "$F" >/tmp/o 2>&1 ); rc=$?; e=$(date +%s.%N); echo "$(echo "$e-$s"|bc)s rc=$rc $(tail -1 /tmp/o) $F"`. Note which OOM (`bad_alloc`) vs solve vs timeout. Save to `/tmp/baseline_perf.txt`.
- [ ] **Step 4:** Report the baseline (regression pass/total/unsound; the 8 sentinel timings/verdicts). This is the reference for Task 4. Do not edit code yet.

---

### Task 1: `SmallVector` ordering ops + `FlatMonomialMap<V>` utility

**Files:** `src/util/SmallVector.h`, `src/theory/arith/poly/FlatMonomialMap.h` (new), `tests/unit/test_flat_monomial_map.cpp` (new).

- [ ] **Step 1 (tests first):** Create `tests/unit/test_flat_monomial_map.cpp`:
```cpp
#include <doctest/doctest.h>
#include "theory/arith/poly/FlatMonomialMap.h"
#include "expr/types.h"
#include <gmpxx.h>
using namespace zolver;
using Key = FlatMonomialMap<mpq_class>::Key;   // SmallVector<pair<VarId,int>,4>

static Key k(std::initializer_list<std::pair<VarId,int>> xs){ Key key; for(auto&p:xs) key.push_back(p); return key; }

TEST_CASE("FMM: append + canonicalize merges duplicates, strips zero, sorts") {
    FlatMonomialMap<mpq_class> m;
    m.append(k({{VarId{2},1}}), mpq_class(1));
    m.append(k({{VarId{1},1}}), mpq_class(2));
    m.append(k({{VarId{2},1}}), mpq_class(-1));   // merges with first -> 0 -> stripped
    m.canonicalize();
    REQUIRE(m.size() == 1);                        // only var1 term survives
    CHECK(m.begin()->first == k({{VarId{1},1}}));
    CHECK(m.begin()->second == mpq_class(2));
}
TEST_CASE("FMM: operator[] insert-or-accumulate keeps canonical, find works") {
    FlatMonomialMap<mpq_class> m;
    m[k({{VarId{3},2}})] += mpq_class(5);
    m[k({{VarId{1},1}})] += mpq_class(7);
    m[k({{VarId{3},2}})] += mpq_class(1);          // accumulate
    CHECK(m.size() == 2);
    auto it = m.find(k({{VarId{3},2}}));
    REQUIRE(it != m.end());
    CHECK(it->second == mpq_class(6));
    CHECK(m.find(k({{VarId{9},1}})) == m.end());
    // sorted: var1 before var3
    CHECK(m.begin()->first == k({{VarId{1},1}}));
    CHECK(m.rbegin()->first == k({{VarId{3},2}}));
}
TEST_CASE("FMM: operator== is canonical equality; SmallVector ordering ops") {
    Key a = k({{VarId{1},1},{VarId{2},1}});
    Key b = k({{VarId{1},1},{VarId{2},1}});
    Key c = k({{VarId{1},2}});
    CHECK(a == b); CHECK(!(a == c)); CHECK((a < c)); CHECK(!(c < a));   // lex on (varId,exp): a=[(1,1),(2,1)] < c=[(1,2)]
    FlatMonomialMap<mpq_class> m1, m2;
    m1[a] += 3; m2[b] += 3;
    CHECK(m1 == m2);
    m2[c] += 1; CHECK(!(m1 == m2));
}
TEST_CASE("FMM: move is cheap (moved-from empty), copy preserves") {
    FlatMonomialMap<mpq_class> m; m[k({{VarId{1},1}})] += 4;
    FlatMonomialMap<mpq_class> mv = std::move(m);
    CHECK(mv.size() == 1); CHECK(m.size() == 0);   // moved-from empty (vector move)
    FlatMonomialMap<mpq_class> cp = mv;
    CHECK(cp == mv);
}
```
- [ ] **Step 2:** Build → FAIL (`FlatMonomialMap.h` missing). New file → `cd build && cmake .. >/dev/null && cd ..` then `( ulimit -v 4000000; cmake --build build -j2 )`.
- [ ] **Step 3a:** Add to `src/util/SmallVector.h` (free functions in `namespace zolver`, after the class):
```cpp
template <typename T, size_t N>
bool operator==(const SmallVector<T,N>& a, const SmallVector<T,N>& b) {
    if (a.size() != b.size()) return false;
    for (size_t i = 0; i < a.size(); ++i) if (!(a[i] == b[i])) return false;
    return true;
}
template <typename T, size_t N>
bool operator<(const SmallVector<T,N>& a, const SmallVector<T,N>& b) {
    size_t n = a.size() < b.size() ? a.size() : b.size();
    for (size_t i = 0; i < n; ++i) {
        if (a[i] < b[i]) return true;
        if (b[i] < a[i]) return false;
    }
    return a.size() < b.size();
}
```
(`std::pair` already has `==`/`<`, so element compares work.)
- [ ] **Step 3b:** Create `src/theory/arith/poly/FlatMonomialMap.h`:
```cpp
#pragma once
#include "expr/types.h"
#include "util/SmallVector.h"
#include <vector>
#include <utility>
#include <algorithm>

namespace zolver {

// Flat sorted-vector map keyed by a monomial (sorted (VarId,exp) list).
// Canonical form (after canonicalize() / operator[] inserts): entries sorted
// strictly-ascending by key, unique keys, no zero-V entries. Requires V to be
// default-constructible, == comparable, and += accumulable.
template <typename V>
class FlatMonomialMap {
public:
    using Key = SmallVector<std::pair<VarId, int>, 4>;
    using Entry = std::pair<Key, V>;
    using Storage = std::vector<Entry>;
    using const_iterator = typename Storage::const_iterator;
    using const_reverse_iterator = typename Storage::const_reverse_iterator;

    bool empty() const { return v_.empty(); }
    size_t size() const { return v_.size(); }
    void clear() { v_.clear(); }
    void reserve(size_t n) { v_.reserve(n); }

    const_iterator begin() const { return v_.begin(); }
    const_iterator end()   const { return v_.end(); }
    const_reverse_iterator rbegin() const { return v_.rbegin(); }
    const_reverse_iterator rend()   const { return v_.rend(); }
    const Entry& front() const { return v_.front(); }
    const Entry& back()  const { return v_.back(); }

    // Binary-search lookup (assumes canonical). Returns end() if absent.
    const_iterator find(const Key& key) const {
        auto it = std::lower_bound(v_.begin(), v_.end(), key,
            [](const Entry& e, const Key& kk){ return e.first < kk; });
        if (it != v_.end() && !(key < it->first) && !(it->first < key)) return it;
        return v_.end();
    }

    // Insert-or-accumulate, maintaining canonical order (O(n) shift). For cold
    // paths and the terms_[key]+=coeff idiom; hot build should use append()+canonicalize().
    V& operator[](const Key& key) {
        auto it = std::lower_bound(v_.begin(), v_.end(), key,
            [](const Entry& e, const Key& kk){ return e.first < kk; });
        if (it != v_.end() && !(key < it->first) && !(it->first < key)) return it->second;
        it = v_.insert(it, Entry{key, V()});
        return it->second;
    }

    // Unsorted O(1) append; call canonicalize() before any query/iteration.
    void append(Key key, V val) { v_.emplace_back(std::move(key), std::move(val)); }

    // Sort by key, merge duplicates by += , drop zero-V entries.
    void canonicalize() {
        std::stable_sort(v_.begin(), v_.end(),
            [](const Entry& a, const Entry& b){ return a.first < b.first; });
        size_t w = 0;
        for (size_t r = 0; r < v_.size(); ) {
            Key key = std::move(v_[r].first);
            V acc = std::move(v_[r].second);
            size_t s = r + 1;
            while (s < v_.size() && !(v_[s].first < key) && !(key < v_[s].first)) {
                acc += v_[s].second; ++s;
            }
            if (!(acc == V())) { v_[w].first = std::move(key); v_[w].second = std::move(acc); ++w; }
            r = s;
        }
        v_.resize(w);
    }

    bool operator==(const FlatMonomialMap& o) const { return v_ == o.v_; }
    bool operator!=(const FlatMonomialMap& o) const { return !(v_ == o.v_); }

private:
    Storage v_;
};

} // namespace zolver
```
- [ ] **Step 4:** Build + run `./build/tests/zolver_unit_tests --test-case="FMM:*"` → all PASS.
- [ ] **Step 5:** Commit `feat(util): FlatMonomialMap<V> flat sorted-vector monomial map + SmallVector ordering ops`. No co-author line.

---

### Task 2: Migrate `RationalPolynomial` to `FlatMonomialMap<mpq_class>`

**Files:** `RationalPolynomial.{h,cpp}`.

- [ ] **Step 1:** In `RationalPolynomial.h`: change `using MonomialKey = std::vector<...>` → `using MonomialKey = FlatMonomialMap<mpq_class>::Key;` (i.e. `SmallVector<std::pair<VarId,int>,4>`); include `FlatMonomialMap.h`; change member `std::map<MonomialKey,mpq_class> terms_;` → `FlatMonomialMap<mpq_class> terms_;`; change `const std::map<MonomialKey,mpq_class>& terms() const` → `const FlatMonomialMap<mpq_class>& terms() const`. Remove the now-unused `<map>` include if nothing else needs it.
- [ ] **Step 2:** In `RationalPolynomial.cpp`, adapt every `terms_` mutation to the new surface (read the whole file; key sites):
  - `terms_[key] += coeff`, `terms_[{}] = c`, `terms_[{{v,e}}] = c`: these compile unchanged against `FlatMonomialMap::operator[]` (insert-or-accumulate, canonical) — but they are O(n) per call. For the **hot build ops** (`operator*`, `operator+`, `operator-`, `pow`, `multiplyKeys` accumulation): rewrite to `append()` all product/sum terms into a fresh `FlatMonomialMap`, then `canonicalize()` once (O(m log m)), instead of repeated `operator[]`. Cold mutators (`addTerm`/`addVar`/`addConstant`, `fromConstant`/`fromVar`) can keep `operator[]`/append+canonicalize as convenient.
  - `MonomialKey` is now a `SmallVector`; `multiplyKeys`/`powKey`/`canonicalizeMonomialKey` build `MonomialKey` via `push_back` — `SmallVector` supports it. `std::sort` on a `SmallVector` works (random-access iterators). Verify `canonicalizeMonomialKey`'s `std::sort`/`erase` compile against `SmallVector` (it has `begin/end`; if it lacks `erase`, rewrite that merge to build a fresh key — do NOT change its semantics).
  - `normalize()`: becomes `terms_.canonicalize()` (the FlatMonomialMap already sorts+merges+strips zeros). Confirm it reproduces the old normalize semantics exactly (old normalize merged like terms, dropped zeros, canonical order — identical).
  - Iteration sites (`for (auto& [key,coeff] : terms_)`) are unchanged.
- [ ] **Step 3:** Build the arith library; fix compile errors in `RationalPolynomial.cpp` only (consumer sites are Task 3).
- [ ] **Step 4:** Run the RationalPolynomial unit tests: `./build/tests/zolver_unit_tests --test-case="*RationalPolynomial*" --test-case="*rational*polynomial*"` plus `tests/unit/test_rational_polynomial.cpp` / `test_polynomial.cpp` / `test_polynomial_canonical.cpp` cases. They must PASS (note: `test_polynomial*` has `.at()` map-dependent calls — those are Task 3, may not compile yet; if so, build+run only the rational-polynomial-algebra cases here and defer the rest to Task 3).
- [ ] **Step 5:** Commit `refactor(nra): RationalPolynomial::terms_ uses FlatMonomialMap (SmallVector keys, flat sorted, move-cheap)`. No co-author line.

---

### Task 3: Fix the 6 map-dependent consumer sites + whole-tree build

**Files (from the blast-radius survey):**
- `src/theory/arith/presolve/BoundChainComposer.cpp:12-13` — `.find(key)` + `.end()`: `FlatMonomialMap::find` returns the same iterator semantics → should compile unchanged. Verify.
- `src/theory/arith/nra/projection/LazardProjectionClosure.cpp:27,53` and `ProjectionClosure.cpp:43` — `.rbegin()->second`: `FlatMonomialMap::rbegin()` provided → compiles unchanged. Verify (or switch to `.back().second`).
- `src/theory/arith/presolve/PolynomialEqualityCombination.cpp:111` — `.begin()->second`: provided. Verify.
- Tests `test_polynomial*.cpp`, `test_lazard*.cpp`, `test_squarefree.cpp` — `.at()` / `.rbegin()` / `MonomialKey{...}` literals: `FlatMonomialMap` has no `.at()`. Either add `const V& at(const Key&) const` (asserting present) to `FlatMonomialMap`, OR rewrite those test assertions to `find()`. Prefer adding `at()` (cheap, useful) so tests stay close to original. `MonomialKey{{xv,50}}` literals: `SmallVector` supports brace-init from `initializer_list`? If not, build via `push_back` in a small test helper.

- [ ] **Step 1:** Build the whole tree (`( ulimit -v 4000000; cmake --build build -j2 )`); fix each compile error at the sites above minimally (prefer the FlatMonomialMap surface matching the map call; add `at()` to FlatMonomialMap if tests need it).
- [ ] **Step 2:** Run the projection/presolve/poly unit groups: `--test-case="CDCAC*" --test-case="P2b*" --test-case="*lazard*" --test-case="*quarefree*" --test-case="*olynomial*" --test-case="*resolve*"` → all PASS.
- [ ] **Step 3:** Full unit suite: `( ulimit -v 4000000; ./build/tests/zolver_unit_tests ) 2>&1 | tail -3` → all pass (baseline count + the new FMM cases).
- [ ] **Step 4:** Commit `refactor(nra): adapt 6 map-dependent term-store consumers to FlatMonomialMap surface`. No co-author line.

---

### Task 4: Validation gate (0 verdict change) + NRA perf re-measure

**Files:** none (measurement; append results to this plan).

- [ ] **Step 1:** Full regression: `( ulimit -v 4000000; python3 tools/run_regression.py --root tests/regression --solver build/bin/zolver --timeout 20 -j 2 ) 2>&1 | tee /tmp/post_regression.txt | tail -8`. **MUST equal the Task-0 baseline: same pass/total, 0 UNSOUND, 0 newly-failing case.** `diff` the summaries; if ANY case changed verdict, STOP and investigate (canonical form not preserved = a bug).
- [ ] **Step 2:** Perf re-measure the 8 sentinels (same commands as Task 0 Step 3) and compare to `/tmp/baseline_perf.txt`: `nra_124` (expect ≤ ~5.7s, ideally faster; still `sat`), `kissing_2_2/2_3/2_4`, `hong_5/6/7`, and the `hycomp ball_count global_10` OOM case (expect: less memory; ideally no `bad_alloc` / solves or times out cleanly instead of OOM). Record before/after.
- [ ] **Step 3:** Optional deeper win check: re-time `hong_10` + `hycomp` default-path (the original timeout cases) before/after — any that now solve within 20s are recoveries.
- [ ] **Step 4:** Append a results block: regression OFF==baseline confirmation (0 verdict change, 0 unsound), the 8-sentinel before/after table, OOM outcome, and any recoveries. The win criterion: **0 verdict change + measurable allocation/time reduction on the sentinels (especially the OOM case no longer OOMing)**. If verdicts are identical but perf didn't improve, report honestly (the representation is lighter but the hot cost was elsewhere) — same discipline as surgery #1.
- [ ] **Step 5:** Commit the results block. This refactor is default-path (not flag-gated); promotion = it's already live once Task 4 confirms 0 verdict change. Recommend to master with the perf delta; note the deferred `magCache_` drop-in for the integrated bit-blast.

---

## Self-Review
- Verdict-safety rests entirely on canonical-form preservation (sorted/unique/zero-stripped) — unit-tested in Task 1 (FMM canonicalize) and proven end-to-end in Task 4 (regression == baseline). Task 0 captures the baseline FIRST so the gate is real.
- Blast radius is the mapped 6 sites + SmallVector ops; `FlatMonomialMap` deliberately mimics the `std::map` surface (find/rbegin/front/at/==/[]) so most of the ~34 iteration sites and the 6 map-dependent sites compile unchanged.
- Hot `operator*`/`+` use append+canonicalize (O(m log m)) to avoid O(n²) sorted inserts — the perf intent.
- `magCache_` (A6) is explicitly OUT of scope; `FlatMonomialMap<V>` is templated so it's a later drop-in for the integrated bit-blast, no rewrite.
- Not flag-gated (representation refactor); safety is empirical 0-verdict-change, not a toggle.
