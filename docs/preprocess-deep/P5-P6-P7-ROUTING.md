# P5 / P6 / P7 — small-logic clusters: all engine-bound, hypotheses refuted by structure

**Lane:** preprocess-deep · **Date:** 2026-06-01 · WSL-safe diagnosis.
Across the small-logic high-gap clusters, the proposed PP hypotheses do not match
the actual formula structure; each is engine-bound. Routed accordingly.

## P5 — QF_ANIA (+103) / QF_AUFNIA (+17)
- All 157+17 return **unknown** (not timeout): gated by `XOLVER_COMB_ARRAY_NIA`
  (default-OFF). **Enabling it recovers 0/15** (still unknown/TO, 0 unsound) —
  the array+NIA combination engine genuinely can't decide these. Cases are small
  (~6 KB) with div/mod arrays, **0 multiplications**.
- "Pure-array-sat bypass" doesn't apply: the NIA atoms are not eliminated by the
  array constraints (real div/mod reasoning remains). **NIA-architectural ceiling
  (confirmed B2-alt). → NIA lane.** No PP routing lever.

## P6 — QF_UFNRA cas (+25) / sqrtmodinv-hoenicke (+18)
- Hypothesis was mod-2^k / sqrt detection → modular reasoner. **The operators are
  absent**: `cas` (33 KB) = 333 `*` + 44 real `/` + 13 UF, **no sqrt, no mod**;
  `sqrtmodinv/modInvFull` = 72 `*` + 7 `/`, **no literal sqrt/mod** (the name is
  the problem domain). These are nonlinear-REAL (NIA modular-L3 is integer → N/A).
- All timeout (~20 s). gdb hot spot: `RationalPolynomial::toPrimitiveInteger` →
  `LibPolyKernel::mul` (recursive denominator-clearing polynomial multiplication)
  — **NRA polynomial-kernel-bound + UF combination. → cac-deep / NRA lane.**

## P7 — QF_UFNIA Certora (+78)
- UF-heavy combination (sample 205 KB: 17 UF, 687 `and`, 67 ite, only 8 `*`).
  Mostly timeout, some unknown. **UF+NIA combination → EQNA E1** (N-O / interface-eq
  backtrack lifecycle). The PP "split-aware normalize" angle is speculative and
  subordinate to the combination engine; EQNA owns the seam.

## Consolidated (P4–P8)
Every high-gap small-logic cluster diagnosed this round is **engine-bound**, and
the proposed PP levers (Tseitin explosion, mod-2^k routing, array-sat bypass,
sqrt elimination) are **refuted by measurement / structure**:

| task | cluster | gap | bottleneck (measured) | route |
|---|---|---:|---|---|
| P4 | nec-smt | 2596 | LIA simplex `recomputeBeta` | lia-lra-deep |
| P8 | LassoRanker/uart | 416 | LRA simplex `pivot` / `assertLit`; CNF=z3 | lia-lra-deep |
| P5 | ANIA/AUFNIA | 120 | NIA-arch ceiling (gate recovers 0) | NIA |
| P7 | Certora UFNIA | 78 | UF+NIA combination | EQNA |
| P6 | cas/sqrtmodinv | 43 | NRA poly kernel `toPrimitiveInteger` | cac-deep |
| — | Labyrinth | 20 | **14× CNF clauses** (large-OR sharing) | preprocess (niche) |

**The preprocess-deep actionable surface is `convert` (GAUSS, shipped, net-positive)
+ the Labyrinth large-disjunction CNF-sharing niche (+20).** The remaining gap is
theory-engine throughput (LIA/LRA simplex, NRA poly kernel, combination), not
frontend transformation. Measurement discipline: CNF sizes equal z3's on the big
clusters; the hoped-for single Tseitin lever does not exist.
