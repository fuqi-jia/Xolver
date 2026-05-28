# Conflict-Driven Single-Cell CAC — Design Contract (lever 3)

Status: design pinned (pre-implementation), mirroring `LAZARD.md`. Gated behind
`XOLVER_NRA_CAC` (default OFF). Binding contract; modules MUST conform.

## Why (evidence)

Profiling the QF_NRA `20161105-Sturm-MBO` family (the "251 unsolved-medal"
bucket) showed the bottleneck is **`CdcacCore::buildClosure` — the full Collins
projection closure built upfront**. On a 6-variable, high-degree-equality system
the closure is doubly-exponential: even after removing the O(n!) cofactor
`determinant` (`XOLVER_NRA_LIBPOLY_PSC`) and trying every variable-ordering flag,
all cases still time out. cvc5 closes the same cases in 0.01–0.5 s via
**conflict-driven single-cell coverings** (Ábrahám–Davenport–England–Kremer,
"Deciding the Consistency of NRA with a CDS using Cylindrical Algebraic
Coverings", 2021) — it never builds a full closure; it projects only the
polynomials needed to characterize one cell around the current sample.

Sample classification (51/405 @20 s, z3+cvc5 oracle): xolver solves 3, **27
WINNABLE (all UNSAT, cvc5 often <0.5 s)**, 21 frontier. → ~210/405 winnable.

## Binding invariant (same posture as CDCAC/Lazard)

- **SAT** ⇐ only a full sample that exactly validates all original active
  constraints (model-validated; never trust a heuristic).
- **UNSAT** ⇐ only a complete covering of ℝ at the top level, every interval of
  which carries a single-cell characterization built by a **complete** projection
  operator (Lazard or McCallum-with-well-orientedness-checked). Any incomplete
  characterization / inconclusive root step ⇒ **Unknown, never UNSAT**.
- The CAC path is a **late slow path**: it runs only when the cheap front
  (presolve, subtropical SAT-fast-path) and/or the budgeted Collins pass have not
  decided. Collins/Lazard remain available; CAC never overrides a definite Collins
  verdict.

## Algorithm (get_unsat_cover, recursive)

```
get_unsat_cover(level i, sample s = (x_1=a_1,…,x_{i-1}=a_{i-1})):
  I = []                                   # excluded intervals on the x_i axis
  while ∃ a_i ∈ ℝ not covered by I:
    s' = s ∪ {x_i = a_i}                   # pick a sample point in an uncovered gap
    if i == n:                             # full assignment
       if all active constraints hold at s': return SAT(s')
       cell = single-cell char. of the constraint(s) violated at s'   # 1 poly set
    else:
       r = get_unsat_cover(i+1, s')
       if r == SAT: return SAT
       cell = characterize(r.covering, s')        # project r's polys down to level i
    I.add( interval_from_characterization(cell, a_i) )   # the maximal x_i-interval
  return UNSAT covering = I  (+ the projected polynomial set for the caller)
```

- **Sample selection** picks rationals in uncovered gaps (and algebraic numbers at
  interval endpoints); reuse `RealAlg`/`isolateRealRootsViaNorm` + the existing
  sample machinery.
- **`characterize`** (single-cell projection): the only projection done — over the
  polynomials in the recursion's covering, **specialized at the sample prefix**, so
  they stay low-degree. Built from the **Lazard projection operator** we already
  have (`LazardProjectionOperator`, complete ⇒ no well-orientedness precondition),
  NOT a fresh full closure. This is the soundness-critical core.
- **`interval_from_characterization`** isolates the real roots of the
  characterization polys (at the prefix) bracketing `a_i`, giving the maximal
  sign-invariant interval to exclude. Reuse the tower root-isolation + per-cell
  certificate machinery from the Lazard build.

## Soundness obligations (enforced, not asserted)

1. Every excluded interval's characterization is built by the **complete** Lazard
   operator + a complete root isolation; any `LazardIncompleteReason` /
   `RootComparisonInconclusive` ⇒ abandon CAC for this solve ⇒ Unknown (the
   Collins/Lazard backstop already returns the safe verdict).
2. The top-level covering must be **gap-free over all of ℝ** before returning
   UNSAT (a missed gap = false UNSAT). Track coverage with exact rational/algebraic
   interval arithmetic; an inability to prove gap-freeness ⇒ Unknown.
3. `XOLVER_NRA_UNSAT_CERT` (already present): a CAC UNSAT emits the covering +
   per-interval characterization as the certificate; the replay validator checks
   each interval is sign-invariant and the union covers ℝ.
4. Equational-constraint optimization (designate the single equality, project only
   w.r.t. it) is a **completeness/perf refinement layered later**, behind its own
   sub-gate, with McCallum well-orientedness checked or Lazard-EC obligations met.

## Module plan (A→E), each unit-tested before the next

- **A. Interval/covering data structures** (`nra/cac/Covering.{h,cpp}`): exact
  rational⊕algebraic intervals, gap-finding, gap-free check. Pure, unit-tested.
- **B. `characterize` / `interval_from_characterization`** over the Lazard operator
  (`nra/cac/SingleCellProjection.{h,cpp}`). Unit-tested vs known cells.
- **C. `CacEngine::getUnsatCover`** recursion (`nra/cac/CacEngine.{h,cpp}`),
  SAT=validated / UNSAT=gap-free-covering / else Unknown.
- **D. Wiring**: a `nra.cac` reasoner stage (Full-effort, default-OFF
  `XOLVER_NRA_CAC`) AFTER the budgeted Collins/Lazard pass; getModel reports the
  CAC SAT sample (same pattern as the subtropical stage's `satFastModel_`).
- **E. Differential**: Collins-vs-CAC decided verdicts never disagree; broad
  QF_NRA z3/cvc5 differential 0-unsound; Sturm-MBO winnable-bucket recovered.

## Gate

Default-OFF flag + Unknown guardrail. unit + NRA-family reg 177/177 OFF+ON,
0-unsound. Broad QF_NRA z3/cvc5 differential 0-unsound before promotion (server).
Collins default path byte-identical when the flag is OFF.
