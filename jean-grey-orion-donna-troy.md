# Plan: QF_NRA Phase NRA-1 — Polynomial Payload + CdcacSolver Shell (Revised)

## Goal
Unblock the QF_NRA end-to-end pipeline:
- `Atomizer` extracts polynomial constraints (not just linear).
- `CdcacSolver::check()` handles **trivial constant polynomial constraints** exactly.
- Non-constant constraints return `Unknown` (sound).
- No more `unsupportedTheorySeen_` blocking on every NRA atom.

This is **Phase NRA-1** from the canonical design doc (§24).

---

## Codebase State (post-trail-refactor commit `d4dc17f`)

| Component | Status |
|-----------|--------|
| `CdcacSolver` interface | ✅ Skeleton; `check()` returns `Unknown`; stores `constraints_` / `trail_` |
| `PolynomialKernel` | ✅ Basic ops + `sgn`; libpoly backend available |
| `PolynomialConverter` | ✅ IR → PolyId for arithmetic exprs |
| `TheoryAtomRegistry` | ✅ Stores `PolynomialAtomPayload`; no factory/dedup yet |
| `Atomizer` | ❌ Only `extractLinearConstraint`; non-linear → `setUnsupportedTheorySeen()` |
| `Solver.cpp` NRA wiring | ✅ Registers `CdcacSolver`; blocked by atomizer |
| End-to-end NRA tests | ❌ None committed |

**Blocker**: `Atomizer.cpp:127-129` — `extractLinearConstraint` fails on `x^2`, then `registry_->setUnsupportedTheorySeen()` is called, causing `Solver.cpp` to return `Unknown` **before** `sat->solve()`.

---

## Approach

Single approach: implement Phase NRA-1 exactly per design doc §24.
No alternatives needed — the scope is clearly bounded (unblock pipeline + trivial constants).

---

## File-by-File Plan

### 1. `src/sat/Atomizer.h` (+25 lines)

Add polynomial extraction capability:

```cpp
#include "theory/arith/poly/PolynomialKernel.h"
#include "theory/arith/poly/PolynomialConverter.h"

class Atomizer {
public:
    // ... existing methods ...
    void setPolynomialKernel(PolynomialKernel* kernel);

private:
    // ... existing members ...
    PolynomialKernel* polyKernel_ = nullptr;
    std::unique_ptr<PolynomialConverter> polyConverter_;

    // NEW: extract polynomial constraint for QF_NRA (covers linear + nonlinear)
    bool extractPolynomialConstraint(ExprId eid, const CoreIr& ir, SatVar v);
};
```

### 2. `src/sat/Atomizer.cpp` (+70 lines)

In `atomizeRec`, in the `default` branch (theory comparison kinds):

**Step 1**: Branch on `defaultTheory_`.

```cpp
if (defaultTheory_ == TheoryId::NRA) {
    // Under QF_NRA, ALL arithmetic comparison atoms (including linear)
    // must be registered as PolynomialAtomPayload and routed to TheoryId::NRA.
    // Only CdcacSolver is registered for NRA; linear payloads would be orphaned.
    if (polyKernel_ && extractPolynomialConstraint(eid, ir, v)) {
        // registered inside extractPolynomialConstraint
    } else {
        registry_->setUnsupportedTheorySeen();
    }
} else {
    // Existing LRA/LIA path.
    if (extractLinearConstraint(eid, ir, v)) {
        // registered as LinearAtomPayload
    } else {
        registry_->setUnsupportedTheorySeen();
    }
}
```

**Step 2**: Implement `extractPolynomialConstraint`:

```cpp
bool Atomizer::extractPolynomialConstraint(ExprId eid, const CoreIr& ir, SatVar v) {
    const auto& e = ir.expr(eid);
    if (e.children.size() != 2) return false;  // arity check (see Distinct note below)

    polyConverter_->clearMemo();  // or create fresh if no clearMemo method
    PolyId lhsPoly = polyConverter_->convert(e.children[0], ir);
    PolyId rhsPoly = polyConverter_->convert(e.children[1], ir);
    if (lhsPoly == NullPoly || rhsPoly == NullPoly) return false;

    // Reject non-integer rational constants until LibPolyKernel::mkConst is fixed.
    // If convert() produced a polynomial with non-integer rational coeff,
    // treat as unsupported for Phase NRA-1.
    // (Implementation: in PolynomialConverter, if a rational constant has denom != 1,
    //  return NullPoly to trigger unsupported.)

    PolyId diff = polyKernel_->sub(lhsPoly, rhsPoly);

    Relation rel;
    switch (e.kind) {
        case CoreExprKind::Eq:       rel = Relation::Eq;  break;
        case CoreExprKind::Distinct: rel = Relation::Neq; break;
        case CoreExprKind::Lt:       rel = Relation::Lt;  break;
        case CoreExprKind::Leq:      rel = Relation::Leq; break;
        case CoreExprKind::Gt:       rel = Relation::Gt;  break;
        case CoreExprKind::Geq:      rel = Relation::Geq; break;
        default: return false;
    }

    registry_->registerParsedTheoryAtom(
        v, eid, TheoryId::NRA,
        PolynomialAtomPayload{diff, rel, mpq_class(0)});
    return true;
}
```

Note: `PolynomialConverter::convert` clears its memo each call, so it can be reused.

**Distinct arity note**: Phase NRA-1 explicitly supports only binary `distinct`. If `e.children.size() != 2`, return `false` → unsupported. N-ary distinct (e.g. `(distinct a b c)`) can be expanded to pairwise disequalities in a later phase.

### 3. `src/api/Solver.cpp` (+10 lines)

In the `QF_NRA || NRA` branch:

```cpp
} else if (logic == "QF_NRA" || logic == "NRA") {
    auto polyKernel = createPolynomialKernel();
    auto* polyKernelRaw = polyKernel.get();
    atomizer.setPolynomialKernel(polyKernelRaw);      // Atomizer borrows; do NOT take ownership
    theoryManager.registerSolver(
        std::make_unique<CdcacSolver>(std::move(polyKernel)));
}
```

And update `defaultTheory_`:

```cpp
if (logic == "QF_LIA" || logic == "LIA") {
    atomizer.setDefaultTheory(TheoryId::LIA);
} else if (logic == "QF_NRA" || logic == "NRA") {   // NEW branch
    atomizer.setDefaultTheory(TheoryId::NRA);
} else {
    atomizer.setDefaultTheory(TheoryId::LRA);
}
```

Rationale: `Atomizer` borrows a raw pointer to the **same** `PolynomialKernel` instance that `CdcacSolver` owns via `unique_ptr`. `PolynomialId` is kernel-local and cannot cross kernel instances. `Atomizer` does not take ownership; lifetime is guaranteed because both `atomizer` and `theoryManager` live inside `Solver`.

### 4. `src/theory/arith/cad/CdcacSolver.h` (+35 lines)

Restructure per design doc §5:

```cpp
struct ActivePolynomialConstraint {
    PolynomialId poly;
    Relation rel;       // effective relation
    SatLit reason;      // assigned SAT literal
};

struct CdcacTrailEntry {
    int level;
    size_t activeSizeBefore;
};

struct PendingConflict {
    int level;
    TheoryConflict conflict;
};

class CdcacSolver : public TheorySolver {
    // ...
private:
    std::unique_ptr<PolynomialKernel> kernel_;
    std::unique_ptr<PolynomialConverter> converter_;  // keep for potential use

    std::vector<ActivePolynomialConstraint> active_;
    std::vector<CdcacTrailEntry> trail_;
    std::optional<PendingConflict> pendingConflict_;
    bool pendingUnknown_ = false;  // payload mismatch or internal unsupported state

    // Remove: std::unordered_set<std::string> allVars_;
    // Remove: void collectVars(...);
};
```

### 5. `src/theory/arith/cad/CdcacSolver.cpp` (+90 lines)

#### `assertLit()`
```cpp
void CdcacSolver::assertLit(const TheoryAtomRecord& atom, bool value,
                            int level, SatLit reason) {
    const auto* payload = std::get_if<PolynomialAtomPayload>(&atom.payload);
    if (!payload) {
        // Payload mismatch is an internal routing error, NOT a theory conflict.
        // Do not learn ¬reason. Return Unknown instead.
        pendingUnknown_ = true;
        return;
    }

    size_t oldSize = active_.size();
    Relation rel = value ? payload->rel : negateRelation(payload->rel);

    active_.push_back({payload->poly, rel, reason});
    trail_.push_back({level, oldSize});
}
```

#### `backtrackToLevel()`
Fix the size tracking bug: currently stores `constraints_.size()` (size *after* push).
Must store size *before* push.

```cpp
void CdcacSolver::backtrackToLevel(int level) {
    while (!trail_.empty() && trail_.back().level > level) {
        active_.resize(trail_.back().activeSizeBefore);
        trail_.pop_back();
    }
    if (pendingConflict_ && pendingConflict_->level > level) {
        pendingConflict_.reset();
    }
    pendingUnknown_ = false;  // reset on any backtrack
}
```

#### `check()` — trivial constant handling per design doc §8

```cpp
TheoryCheckResult CdcacSolver::check(TheoryLemmaDatabase&) {
    if (pendingConflict_) {
        return TheoryCheckResult::mkConflict(pendingConflict_->conflict);
    }

    if (pendingUnknown_) {
        return TheoryCheckResult::unknown();
    }

    if (active_.empty()) {
        return TheoryCheckResult::consistent();
    }

    std::vector<SatLit> conflictLits;
    bool hasNonConstant = false;

    for (const auto& c : active_) {
        if (!kernel_->isConstant(c.poly)) {
            hasNonConstant = true;
            continue;
        }
        mpq_class val = kernel_->toConstant(c.poly);
        bool ok = false;
        int s = cmp(val, mpq_class(0));
        switch (c.rel) {
            case Relation::Eq:  ok = (s == 0); break;
            case Relation::Neq: ok = (s != 0); break;
            case Relation::Lt:  ok = (s <  0); break;
            case Relation::Leq: ok = (s <= 0); break;
            case Relation::Gt:  ok = (s >  0); break;
            case Relation::Geq: ok = (s >= 0); break;
        }
        if (!ok) {
            conflictLits.push_back(c.reason.negated());
        }
    }

    if (!conflictLits.empty()) {
        return TheoryCheckResult::mkConflict(TheoryConflict{conflictLits});
    }

    if (!hasNonConstant) {
        return TheoryCheckResult::consistent();
    }

    return TheoryCheckResult::unknown();
}
```

#### `reset()`
```cpp
void CdcacSolver::reset() {
    active_.clear();
    trail_.clear();
    pendingConflict_.reset();
    pendingUnknown_ = false;
}
```

### 6. `tests/unit/test_nra.cpp` (new, ~120 lines)

Seven test cases:

**Test 1 — Trivial constant unsat**: `(assert (= 1 0))` → `Result::Unsat`
- Atomizer extracts `1 - 0 = 1` as constant polynomial `Eq 0`.
- CdcacSolver `check()` sees constant, val=1, Eq unsatisfied → conflict.

**Test 2 — Trivial constant sat**: `(assert (> 1 0))` → `Result::Sat`
- Constant polynomial `1`, relation `Gt` → satisfied.
- SAT solver finds trivial model.

**Test 3 — Non-constant returns Unknown**: `(assert (= (+ (* x x) 1) 0))` → `Result::Unknown`
- Atomizer successfully extracts polynomial payload (not blocked).
- CdcacSolver `check()` sees non-constant → `Unknown`.
- This is the **critical regression guard**: proves the atomizer no longer blocks NRA.

**Test 4 — False literal negation**: `(assert (not (> 1 0)))` → `Result::Unsat`
- Tests that negated constant relations are correctly evaluated.
- `not (> 1 0)` becomes `<=`; constant `1 <= 0` is false → conflict.

**Test 5 — Distinct constant unsat**: `(assert (distinct 1 1))` → `Result::Unsat`
- `distinct 1 1` maps to `Neq`; constant `1 != 1` is false → conflict.

**Test 6 — Eq negation constant unsat**: `(assert (not (= 1 1)))` → `Result::Unsat`
- `not (= 1 1)` becomes `Neq`; constant `1 != 1` is false → conflict.

**Test 7 — Non-integer rational constant**: `(assert (= (/ 1 2) 0))` → `Result::Unknown`
- Phase NRA-1 rejects non-integer rational constants (until `LibPolyKernel::mkConst` is fixed).
- `PolynomialConverter` returns `NullPoly` → unsupported → `Unknown`.
- This guards against unsoundness from dropped denominators.

---

## Build & Test Verification

```bash
cd build && cmake --build . -j$(nproc)
./tests/zolver_unit_tests --test-case="NRA*"
./bin/zolver solve /tmp/test_nra_const_unsat.smt2   # expect: unsat
./bin/zolver solve /tmp/test_nra_nonconst.smt2      # expect: unknown (not blocked)
./bin/zolver solve /tmp/test_nra_rational.smt2      # expect: unknown (rejected)
```

---

## Deferred to Later Phases

Per design doc §24:

| Item | Phase |
|------|-------|
| Local search model finder | NRA-3 |
| Root isolation / Sturm sequences | NRA-4 |
| CAD/CDCAC recursive search | NRA-5 |
| Projection / lifting / conflict clauses | NRA-6 |
| Dynamic polynomial lemmas (diseq split) | NRA-7 |
| `getOrCreatePolynomialAtom` dedup | NRA-2+ |
| Proper rational coefficients in `LibPolyKernel::mkConst` | NRA-2+ |
| N-ary distinct expansion | NRA-2+ |

Phase NRA-1 **must not** implement any of the above.

---

## Risks & Mitigations

| Risk | Mitigation |
|------|------------|
| `PolynomialConverter` fails on division / non-integer exponents | Mark unsupported; sound |
| `PolynomialConverter` rejects non-integer rational constants | Returns `Unknown` (sound) until `LibPolyKernel::mkConst` is fixed in NRA-2+ |
| `PolynomialId` cross-kernel misuse | **Atomizer and CdcacSolver share the same `PolynomialKernel` instance**; `Atomizer` holds a raw borrow, `CdcacSolver` holds `unique_ptr` ownership. No second instance. |
| SAT var routing to wrong solver | `registerParsedTheoryAtom` receives explicit `TheoryId::NRA`; `TheoryManager` dispatches by `record.theory` |
| Payload mismatch in `assertLit` | Treated as `pendingUnknown_` (returns `Unknown`), not a fake conflict clause. Safe and sound. |
| Binary-only `distinct` support | Documented limitation; n-ary distinct is deferred to NRA-2+. |
