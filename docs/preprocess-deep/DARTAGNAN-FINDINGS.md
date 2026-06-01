# Dartagnan ReachSafety-Loops — engine-bound, NOT preprocessing-actionable

**Lane:** preprocess-deep · **Date:** 2026-06-01 · **Branch:** agent/preprocess-deep (62d91dd)
**Cluster:** `20210219-Dartagnan/ReachSafety-Loops` — QF_NIA 336 + QF_LIA 117 oracle-decided gap.

## Verdict
**Engine-bound (CDCL(T) theory-propagation scale). Hand off to lia-lra-deep (LIA) + NIA lanes.**
No preprocessing lever in this lane recovers any case. Documented per task step 5.

## Evidence

**1. Oracle decides ~96–99 %, dominantly UNSAT, xolver ~0** (30s batch):
| div | cluster | total | oracle-dec | xolver-dec | sat | unsat |
|---|---|---:|---:|---:|---:|---:|
| QF_NIA | ReachSafety-Loops | 350 | 336 (96%) | 0 | 8 | 328 |
| QF_LIA | ReachSafety-Loops | 118 | 117 (99%) | 1 | 14 | 103 |

**2. Shape = BMC loop-unrolling — big bool + sparse/near-linear arith** (`afnp2014-O0`, QF_LIA, 716 KB):
740 int + **2732 bool** vars, **5352 equalities** (SSA assignments), ~25 inequalities, **19032 `and`**, 36 ite, **0 multiplications**. The QF_NIA cases are **nearly linear** (`array-1-O0`: 1680 int, 2266 bool, 4420 eq, **only 8 multiplications** in 396 KB) — declared-NIA but the nonlinearity is negligible.

**3. z3 solves trivially; xolver times out** — parse is NOT the bottleneck:
`afnp2014-O0`: z3 **unsat 0.41 s**; xolver **parse-only 0.43 s** but **solve times out** at 40 s.

**4. NO preprocessing lever helps** (`afnp2014-O0`, @40 s, no ulimit):
default / `PP_SOLVE_EQS` / `PP_SOLVE_EQS_GAUSS` / `PP_PG_CNF` / `PP_REWRITE` / all-combined → **all timeout**. GAUSS eliminates only **367/740** int vars (most equalities are bool-defining, ITE, or not ±1-isolatable) — the **boolean structure dominates** and var-elimination barely dents it.

**5. Hot spot = theory-propagation loop, not preprocessing** (gdb stack sample):
```
xolver::LiaSolver::assertLit(...)
xolver::CadicalTheoryPropagator::cb_check_found_model(...)
CaDiCaL::Internal::external_check_solution / cdcl_loop_with_inprocessing
```
Thousands of equality-derived theory atoms are asserted/checked **per SAT model** in the CDCL(T) loop. This is theory-propagation scale (cf. the known "heavy work per `cb_propagate`" NIA pattern), which preprocessing cannot address.

**6. Consistent across the cluster** — 6 cases (3 LIA + 3 NIA), default and best-PP, **0 recovery**:
`MADWiFi-encode_ie_ok-O0`, `Mono3_1-O0`, `Mono5_1-O0`, `array-1-O0`, `array-2-O0`, `array_1-1-O0` — all timeout both ways.

## Handoff
- **QF_LIA (117)** → **lia-lra-deep**: `LiaSolver::assertLit` / TheoryManager CDCL(T) incrementality — re-asserting O(atoms) theory literals per `cb_check_found_model` on BMC-scale atom sets is the bottleneck. z3 wins via incremental theory propagation + its simplifier collapsing the SSA equalities.
- **QF_NIA (336)** → **NIA lane**: same theory-propagation scale; the ~8 multiplications don't change the bottleneck (effectively a LIA-scale problem wearing an NIA label).
- **Common root** is the CDCL(T) theory-interaction cost at BMC scale (LiaSolver/TheoryManager/SAT), not frontend folding. Catalog: retag `Dartagnan ReachSafety-Loops` from preprocess-deep → lia-lra-deep + NIA.

## Why preprocessing can't crack it
var-elimination removes int vars, but the cost is in the **boolean+atom interaction** (2732 bools, thousands of equality atoms) under CDCL(T). Even perfect CNF (PG_CNF) doesn't help because the hot path is theory `assertLit`, not SAT solving. The lever is incremental theory propagation — an engine concern.
