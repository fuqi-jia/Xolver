# REDESIGN Day 1 report — Wisa combination model bug

**Date:** 2026-06-02
**Charter:** 3-day R&D budget for internal-bridge-var ownership redesign
**Goal:** Wisa false-SAT class — true fix (correct sat/unsat verdict), not floor

## Architectural audit (P1.1)

Bridge-var lifecycle traced (src/theory/combination/Purifier.cpp:80-92):
- Created by `Purifier::makeFreshVar` named `bridge_N`
- Owners: {Combination, EUF, arithTheory_} (all three)
- `isInternal=true`
- Bridge assertion `(= bridge_N <compound>)` added to `bridgeAssertions_`
- Compound UF arg bridging gated by XOLVER_COMB_SAT_FLOOR or XOLVER_COMB_UFARG_ARRANGE (both default-OFF)

Arrangement skip rationale (TheoryManager.cpp:584):
```cpp
if (!st || st->isInternal) continue;  // scope to user terms only
```
Internal bridge vars are excluded from model-based arrangement splitting.

## Attempt #1: XOLVER_COMB_ARRANGE_INTERNAL (P1.2 Option A-style)

**Hypothesis:** Include internal bridge vars in arrangement → bridge_v and user-var
that arith assigns to the same value get split → if equality forced, EUF congruence
fires → conflict detected.

**Variants tested:**
1. **v1:** include internals + standard `allowInterfaceDiseqModelBranch` for all pairs
   - Result on Wisa(15) 15s: 0 correct, 13 unknown, **2 wrong** (regression)
2. **v2:** include internals but SKIP `allowInterfaceDiseqModelBranch` for internal vars
   (bridge_v value is pinned by bridge assertion; allowing arith diseq-branch was
   bypassing the bridge constraint)
   - Result on Wisa(15) 15s: 0 correct, 11 unknown, **4 wrong** (worse)

**Verdict:** REJECTED. Both variants destabilize the existing COMB_VALIDATE_SAT
floor without producing correct verdicts. The arrangement-splitter extension
doesn't address the actual bug.

## Attempt #2: in-search blocking-clause validator (P2-prototype)

**Hypothesis:** When validator detects Violated model AT cb_check_found_model
(inside SAT search), build a blocking clause from the SAT model and inject it
as a Conflict → CaDiCaL backtracks and continues. This replaces the post-solve
floor's "Unknown" with in-search clause learning that drives the search to
either a valid sat or true UNSAT.

**Implementation:**
- `CadicalTheoryPropagator::setExternalModelValidator` hook
- After `tm_.check` returns Consistent at Full effort, call validator
- If validator returns blocking clause, enqueue as pending conflict, return false
- CaDiCaL learns the clause and continues

**Result on Wisa(15) 8s:** 0 correct, 15 unknown, 0 wrong.

**Analysis:** Sound (no false-SAT, no false-UNSAT). But no correct verdicts —
the blocking-clause approach is exponentially slow on Wisa-shape. Each blocking
clause excludes ONE complete SAT assignment from a search space of 8^9 ≈ 134M
possible select_format value assignments. SAT cannot enumerate fast enough
within reasonable timeout.

**Verdict:** SOUND BUT IMPRACTICAL. The architecture works correctly but the
combinatorics make it useless within sprint timeouts. Would need either:
- MUS-style minimum-unsatisfiable-subset clause extraction (multi-week)
- Wisa-specific pattern → bit-blast routing (multi-day)
- Different combination engine (model-based theory combination, multi-week)

## Day 1 conclusion

Both architectural levers attempted (ARRANGE_INTERNAL + in-search blocking
clauses) FAIL to yield correct verdicts within practical timeout. They either
regress (v1, v2) or are sound-but-too-slow (in-search).

**The 3-day R&D budget is insufficient** for this problem. The genuine fix
requires either MUS-style clause extraction or a model-based theory combination
engine — both multi-week.

**Recommended Day 2-3 plan revision:**
- Day 2: investigate Wisa-specific pattern detection (e.g., when negated-goal
  conjunction over UF-arith forces functional consistency, route to bit-blast
  on the finite domain of UF args)
- Day 3: production validate or accept architectural truth

## State

All experiment branches reverted. Tree at `agent/eqna-2 = 8f048af` (unchanged
from before redesign attempts). COMB_VALIDATE_SAT floor stays as the sound
band-aid (13 false-SAT → 0 unknown; 7 true-sat → 7 unknown over-floor).
