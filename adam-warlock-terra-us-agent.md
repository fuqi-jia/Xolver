# EUF Solver Enhancement Plan for Zolver

## Context

Zolver currently has a **working EUF V1 skeleton** with:
- `EufTermManager`: hash-consed term interning (Variable, UFApply, ConstBool)
- `EGraph`: union-find + full-rebuild congruence closure via repeated appTable scan
- `EufSolver`: CDCL(T) TheorySolver interface, full-rebuild `check()`, conflict generation
- `Atomizer`: EUF atom extraction for `=`, `distinct`, n-ary forms, bool predicates
- `Solver.cpp`: QF_UF logic registration

**All 17 regression tests and 18 unit tests pass.**

However, several gaps remain before EUF is a robust, long-term theory solver:
1. **EGraph explanation BFS has a correctness bug** — returns failure on benign re-visits in undirected graphs
2. **No model construction** — `EGraph::buildModel()` is a no-op; SAT results lack EUF model values
3. **No theory propagation** — EUF never emits propagation lemmas for entailed equalities
4. **No mixed-theory support** — QF_UFLIA/UFLRA/UFNIA/UFNRA return `Unknown`

This plan addresses (1)–(3) to make EUF production-ready for pure QF_UF, and lays the groundwork for (4).

---

## Phase 1: Fix Explanation BFS (Critical Correctness Bug)

**File**: `src/theory/euf/EGraph.cpp`

**Problem**: `explainPath()` returns `{false, {}}` when BFS encounters a node already in `parentTerm`. In an undirected explanation graph, multiple paths between nodes are normal (e.g., transitivity chains forming cycles). The current logic incorrectly treats any re-visit as an error.

**Fix**:
- Remove the `visitedPairs`/`parentTerm.find(next)` early-failure logic.
- Use standard BFS: track `parentTerm` and `parentEdge`; skip `next` only if already visited.
- Remove the `pairKey` cycle detection that incorrectly aborts.
- Add unit tests for cyclic explanation graphs:
  - `a=b`, `b=c`, `c=a` (cycle) + `f(a)!=f(c)` should still explain correctly.

**Acceptance**: New cyclic-explanation unit tests pass; all existing 18 EUF unit tests still pass.

---

## Phase 2: EUF Model Construction

### 2a. EGraph model builder

**File**: `src/theory/euf/EGraph.cpp` / `EGraph.h`

Implement `buildModel()` to produce:

```cpp
struct EufClassValue {
    EClassId classId;
    std::string value;       // e.g., "ufval_0"
};

struct EufFunctionEntry {
    std::vector<std::string> argValues;  // class values of arguments
    std::string resultValue;             // class value of result
};

struct EufFunctionInterp {
    std::string name;
    std::vector<EufFunctionEntry> entries;
    std::string defaultValue;
};

struct EufModel {
    std::unordered_map<EClassId, std::string> classValues;
    std::unordered_map<FuncSymbolId, EufFunctionInterp> functions;
};
```

Algorithm:
1. For each equivalence class, assign a unique string value (`"ufval_N"`).
2. For each function application term `f(t1,...,tn)`:
   - Compute `key = (class(t1), ..., class(tn))`.
   - Record `functions[f].entries[key] = class(f(t1,...,tn))`.
3. Congruence closure guarantees no conflicting entries; assert this.

### 2b. EufSolver model integration

**File**: `src/theory/euf/EufSolver.cpp` / `EufSolver.h`

- Add `EufModel model_;` member.
- Populate it in `check()` after consistency is confirmed.
- Expose `const EufModel& model() const`.

### 2c. Solver API model output

**File**: `src/api/Solver.cpp`

- In `checkSatInternal()`, after SAT is confirmed, if logic is QF_UF, retrieve the EUF model from `EufSolver` and store it for `getModel()`.
- `getModel()` should return class assignments for user-visible constants and function interpretations.

**Acceptance**: 
- `zolver solve --produce-models` on `euf_001_sat_basic_eq.smt2` outputs a model with class assignments.
- Model respects congruence: if `a=b`, they have the same value.

---

## Phase 3: Theory Propagation

**File**: `src/theory/euf/EufSolver.cpp` / `EufSolver.h`

### 3a. Registered atom tracking

`EufSolver` already receives all EUF atoms via `assertLit`. Add:

```cpp
std::vector<EufAtom> registeredAtoms_;  // all unique equality atoms seen
```

Populate from `trail_` during `check()` (deduplicate by `satVar`).

### 3b. Propagation detection

After `closeCongruence()`, iterate `registeredAtoms_`:

```cpp
for (auto& atom : registeredAtoms_) {
    if (atom.rel != Relation::Eq) continue;
    if (atom already assigned in SAT) continue;   // need SAT query interface
    if (egraph_.same(atom.lhs, atom.rhs)) {
        auto explain = egraph_.explainEquality(atom.lhs, atom.rhs, termManager_);
        if (explain.ok) {
            // lemma: ¬reasons ∨ atom.lit
            std::vector<SatLit> clause;
            for (SatLit r : explain.reasons) clause.push_back(r.negated());
            clause.push_back(atom.assertedLit);
            return TheoryCheckResult::mkLemma(TheoryLemma{std::move(clause)});
        }
    }
}
```

**Note**: Detecting "already assigned" requires querying the SAT solver. If the current `TheoryCheckResult` / `TheoryLemmaDatabase` interface does not expose SAT assignment state, V3 can skip the "assigned" filter and let the SAT solver ignore redundant lemmas.

### 3c. Negative propagation (optional V3)

EUF does not naturally entail disequalities except via:
- Active disequality atoms
- Disjoint sorts (if sort system supports it)
- True ≠ False (already handled)

Skip negative propagation in V3.

**Acceptance**: Add a unit test where `a=b` is asserted and `(f a)=(f b)` is unassigned; EUF should propagate it (indirectly verified by an UNSAT test where the negation of the propagated atom causes conflict).

---

## Phase 4: Mixed-Theory Skeleton (Prep for Nelson-Oppen)

**File**: `src/api/Solver.cpp`

### 4a. Purification detection

In `checkSatInternal()`, for QF_UFLIA/UFLRA/UFNIA/UFNRA:
- Instead of returning `Unknown` immediately, check if the problem is **pure** in one theory.
- If no UF terms appear, fall back to the pure arithmetic solver.
- If UF terms appear but no arithmetic, fall back to pure QF_UF.
- Only return `Unknown` if the problem genuinely mixes theories.

### 4b. Shared equality atom registry (design-only)

Add a design comment in `Solver.cpp` or a new header `src/theory/combination/EqualityManager.h` (skeleton only):

```cpp
// EqualityManager: future home for Nelson-Oppen shared equality propagation.
// Responsibility:
//   1. Maintain shared equality atoms between EUF and arithmetic solvers.
//   2. Broadcast EUF-derived shared equalities to arithmetic.
//   3. Broadcast arithmetic-derived shared equalities to EUF.
//   4. Generate arrangement lemmas for shared variables.
// Not implemented in V1.
```

**Acceptance**: `Solver.cpp` has a clear TODO/comment explaining the V2 combination path.

---

## Phase 5: Testing & Hardening

### 5a. New unit tests (tests/unit/test_euf.cpp)

1. **Cyclic explanation**:
   ```smt2
   (assert (= a b))
   (assert (= b c))
   (assert (= c a))
   (assert (distinct (f a) (f c)))
   ```
   → unsat with valid explanation.

2. **Model output**:
   Run `sat` cases with `--produce-models` and verify model assigns same value to merged classes.

3. **Propagation indirect test**:
   ```smt2
   (assert (= a b))
   (assert (not (= (f a) (f b))))
   ```
   → unsat (this already passes; verify it uses propagation path or at least conflict path).

### 5b. Regression tests (tests/regression/euf/)

Add:
- `euf_018_unsat_cyclic_explanation.smt2`
- `euf_019_sat_model_production.smt2` (for manual model-check testing)

### 5c. AGENTS.md update

Update `AGENTS.md` EUF status:

```text
| E | EufSolver (EUF) | ✅ V1 functional | Congruence closure, conflict, explanation |
| E | EufSolver (EUF) | 🏗️ Phase 2 | Model construction, theory propagation |
| F | EqualityManager | 🏗️ Skeleton | Nelson-Oppen combination prep |
```

---

## File Changes Summary

| File | Action |
|------|--------|
| `src/theory/euf/EGraph.cpp` | Fix BFS explanation bug; implement `buildModel()` |
| `src/theory/euf/EGraph.h` | Add `EufModel` struct; update `buildModel()` signature |
| `src/theory/euf/EufSolver.cpp` | Add model construction call; add propagation loop |
| `src/theory/euf/EufSolver.h` | Add `model()`, `registeredAtoms_` |
| `src/theory/euf/EufTypes.h` | Add `EufModel` structs if not in `EGraph.h` |
| `src/api/Solver.cpp` | Integrate EUF model into `getModel()`; update mixed-logic comments |
| `tests/unit/test_euf.cpp` | Add cyclic explanation + model tests |
| `tests/regression/euf/` | Add 2 new regression files |
| `AGENTS.md` | Update EUF status |

---

## Key Red Lines

1. **Explanation must never fail on benign BFS revisits** — fix in Phase 1.
2. **Model values must respect congruence** — same class → same value.
3. **Propagation lemmas must be guarded by explanation reasons** — no bare propagations.
4. **Mixed theories remain `Unknown` in V1** — only purification fallback in Phase 4.
5. **All existing 18 unit tests + 17 regression tests must continue to pass.**
