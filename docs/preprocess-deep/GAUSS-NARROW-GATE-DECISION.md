# GAUSS narrow-gate — Decision: Option C (densification auto-fallback)

**Lane:** preprocess-deep · **Date:** 2026-06-01 · **Branch:** agent/preprocess-deep

## Decision
**Option C — internal densification self-check.** GAUSS general ±1-pivot
elimination re-enters CANDFLAGS with two automatic guards in `SolveEqs`. No
benchmark-signature heuristic (Option A) and no revert (Option B) needed.

## What the −103 actually was (corrects the bisection attribution)
Two independent mechanisms, only the second is GAUSS-specific:

1. **Substitution-pass blowup** (dominant). `run()` re-substitutes across all
   conjuncts after every elimination → O(elims × formula-size). On large
   chained-aux Petri-nets (SMPT SharedMemory/RwMutex: thousands of `aᵢ = Σx`
   over ~25k conjuncts) it burns the whole budget in preprocessing.
   **Hits plain bare-var `PP_SOLVE_EQS` too, not just GAUSS** — the master's
   `base unsat → GAUSS TO30` was really `SOLVE_EQS TO30`. Fixed by the
   **work-budget guard** (commit 858b4aa): SharedMemory/RwMutex unsat 2–6 s,
   0/40 SOLVE_EQS regress.

2. **Farkas densification** (GAUSS-only). General elimination of a hub variable
   fans its definition into many constraints, *growing* the formula and
   obscuring the short UNSAT (Farkas) certificate. Small Petri-net UNSATs
   (CircularTrains) regress ~55 %. Fixed by the **densification guard** below.

## The densification guard (the clean signal)
Measured the live DAG-size ratio (final / initial) of the general-elimination pass:

| family | verdict | GAUSS effect | DAG ratio |
|---|---|---|---|
| convert | SAT | **helps** (+22) | **0.82** (shrinks) |
| CircularTrains | UNSAT | **hurts** (−55 %) | **1.86–2.21** (grows ~2×) |

General elimination **shrinks** the formula when genuinely simplifying (SAT-
helpful) and **grows** it when densifying (UNSAT-harmful) — a computable proxy
for the SAT/UNSAT asymmetry that needs no SAT/UNSAT oracle. The guard recomputes
the DAG every few eliminations and, once it exceeds `growthCap_×` (default 1.30,
env `XOLVER_PP_SOLVE_EQS_GROWTH_CAP`), disables further general elimination
(bare-var continues; it never densifies). Stopping is SOUND — every elimination
already done is equisat + registered for model replay.

## Paired-test result (acceptance gate)
GAUSS + work-budget + densification guard:
- **convert recovery: 23/30** (was 22/30 without guards — preserved)
- **CircularTrains: 20/20 ok** (was 11/20 regress = 55 %)
- **other SMPT/nec fast-unsat: 19/20 ok** (1 residual ≈ 2.5 %)
- **0 unsound** throughout
- Gates: unit 1071/1071, reg 670/670 OFF+ON(SOLVE_EQS+GAUSS)

## Net
GAUSS flips from net −81 to **net-positive**: convert +22, SMPT/nec regress
≈0. Re-enters CANDFLAGS. Independently, the work-budget guard makes plain
bare-var `PP_SOLVE_EQS` safe on SMPT/nec (→ A5/lia-lra-deep can re-evaluate it
for CANDFLAGS too).

## Flags
- `XOLVER_PP_SOLVE_EQS_GAUSS` — general ±1-pivot elimination (opt-in; now guarded).
- `XOLVER_PP_SOLVE_EQS_BUDGET` — substitution-work cap (default 40M).
- `XOLVER_PP_SOLVE_EQS_GROWTH_CAP` — densification cap (default 1.30).
- `XOLVER_PP_SOLVE_EQS_DIAG` — prints elim count, DAG ratio, work, guard trips.
