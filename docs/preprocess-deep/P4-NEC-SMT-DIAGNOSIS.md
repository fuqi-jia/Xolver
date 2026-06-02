# P4 nec-smt — diagnosis: simplex-performance-bound → route to lia-lra-deep

**Cluster:** QF_LIA nec-smt/large (767 gap) + /med (364 gap), 0 xolver-decided,
mixed sat/unsat. nec-smt/small solves 20/35 (tractable at small scale only).

## Structure
Verification/path-condition family — few variables, **dense term-ITE nesting**.
`med/checkpass_pwd/prp-0-19` (23 KB): 25 int vars, **589 ITEs**, 327 eq, 15 muls,
0 bool. The ITEs (not the variables) are the complexity.

## z3 vs xolver
- z3: **sat 0.35 s, 14136 decisions, 886 conflicts** — real *search* (not the
  1-decision preprocessing collapse seen in Dartagnan). The win is a fast
  incremental simplex under heavy CDCL(T) search.
- xolver: **timeout** (parse 0 ms — not parse-bound).

## Bottleneck (gdb)
```
xolver::GeneralSimplex::recomputeBeta   (mpz_init_set per call — GMP alloc heavy)
xolver::GeneralSimplex::check
xolver::LiaSolver::stageCore
ArithSolverBase::runReasonerPipeline  (per cb_check_found_model)
```
The simplex does a **full β (basic-variable value) recompute per theory check**,
called thousands of times across the 589-ITE search. z3's incremental β updates
make the same 14 k-decision search fast.

## PP levers tested — none help
default / `PP_SOLVE_EQS` / `PP_REWRITE` / `PG_CNF` / combined → **0/6 recovery**
(3 med + 3 large), all timeout. No preprocessing transformation addresses
per-check simplex cost.

## Verdict
**Engine-bound: GeneralSimplex incrementality (lia-lra-deep).** Same root class
as Dartagnan (LIA engine cost in the CDCL(T) loop) — there `assertLit`, here
`recomputeBeta`. Both are "full recompute per theory check" inefficiencies.
**Routed to lia-lra-deep** (incremental simplex β / warm-started check). No
preprocess-deep lever; not ship-able from the frontend.

## Consolidated QF_LIA gap note
The big QF_LIA weakness clusters (Dartagnan, nec-smt) are dominated by **LIA
engine performance in the CDCL(T) search loop**, not preprocessing. The
preprocess-deep win in QF_LIA is `convert` (SAT, GAUSS); the UNSAT/search-heavy
remainder is lia-lra-deep's incremental-simplex work.
