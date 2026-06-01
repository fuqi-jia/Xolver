# P4+P8 — Tseitin/CNF-explosion hypothesis: REFUTED on the big clusters

**Lane:** preprocess-deep · **Date:** 2026-06-01
**Hypothesis (master):** one PP-side lever (DAG-aware CNF / lazy Tseitin / ITE
clustering) shrinks the boolean blowup across nec-smt + LRA-boolean = +3100.
**Verdict: refuted by measurement.** xolver's CNF is the same size as z3's on the
large clusters — they are engine-bound, not CNF-bound. Only Labyrinth (+20) has a
real CNF lever.

## Measurement (xolver SAT instance vs z3, via XOLVER_SAT_SIZE_DIAG + z3 -st)

| cluster | gap | xolver vars / clauses | z3 vars / clauses | hot spot |
|---|---:|---|---|---|
| nec-smt/med | 2596 | 3039 / 6590 | ~same scale | `GeneralSimplex::recomputeBeta` |
| LassoRanker | 374 | 2692 / 6488 | ~same scale | `SparseTableau::addCoeff` / `pivot` |
| uart | 42 | 2328 / 5747 | **2065 / 5779** | `LraSolver::assertLit` per notify_assignment |
| Labyrinth | 20 | 76971 / **641437** | 69124 / **46253** | (14× clause blowup) |

**Big clusters (nec-smt, LassoRanker, uart): CNF ≈ z3's.** No Tseitin explosion.
z3 wins via fast/effective LRA theory propagation — uart: z3 closes UNSAT with
2267 decisions + **40189 LP bound-propagations**; xolver re-asserts into the LRA
solver per CaDiCaL assignment and its simplex is slower per check. **Engine-bound
(lia-lra-deep): simplex pivot/β-recompute speed + theory-propagation effectiveness.**
A PP-side CNF lever cannot help — the CNF is already z3-sized.

## The one real CNF lever — Labyrinth (+20, niche)
Labyrinth (12.6 MB, **174747 `or`, 0 `and`**): xolver emits **641 437 clauses**,
z3 only **46 253** — a **14× blowup**. z3's simplifier dedups/shares the giant
disjunction structure; xolver's CNF emits it ~directly (≈3.7 clauses/or). This is
a genuine **DAG-aware / sharing-aware CNF** opportunity (master's option C/D), but
scoped to giant-disjunction formulas — a +20 niche in a non-0% division (QF_LRA),
not the championship prize.

## Conclusion / routing
- **P4 nec-smt (+2596) + P8 LassoRanker (+374) + uart/sc/tta (+112): engine-bound
  → lia-lra-deep** (incremental simplex + LRA bound-propagation). No preprocess
  lever; the CNF is not the problem.
- **Labyrinth (+20): real but niche CNF-sharing lever.** Tractable only if a
  large-disjunction sharing pass is cheap; low priority vs the 0%-division
  small-logic wins (P5/P6/P7).
- The "single +3100 Tseitin lever" does not exist; the boolean-heavy slowness is
  theory-throughput, measured identical CNF to z3.

Diagnostic shipped: `XOLVER_SAT_SIZE_DIAG` (prints CaDiCaL var/active/clause counts
at each solve()) — reusable for any future CNF-size investigation.
