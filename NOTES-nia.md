# NOTES-nia (Agent NIA, branch agent/nia-2)

Running notes. Branch `agent/nia-2` (integrated main + my work). Commit+push per lever.
Gates every lever: default-OFF flag, 0-unsound, nia reg 113/113 OFF+ON, self-measure via eval/.

## Shipped (verified + pushed)
- **L3 modular residue reasoner** `XOLVER_NIA_MODULAR` (enum path): sound constant-pow2-modulus
  UNSAT via div/mod quotient elimination + residue enumeration. (2d78819, b8968ed)
- **Hensel/Newton-doubling** (same flag): lifts past enum cap. ENTIRE modInv family
  modInv8..modInvFull (incl 2^256) TIMEOUT→unsat. (55e56aa)
- **WalkSAT SLS** `XOLVER_NIA_LOCALSEARCH` (lever #2 SAT-side): discrete-Newton critical moves +
  restarts, candidate-only/validator-gated. (8d94dff)
- Gates held: unit 883/883, nia reg 113/113 each flag OFF+ON, 0-unsound.

## Certora QF_UFNIA finding (validated, not assumed)
L3/Hensel does NOT apply to the real Certora EVM cases: they are bytecode-derived WRAPPING
`mod 2^256` (ite int256<->uint256) + UF + hashing, not modular-inverse Newton chains. z3 also
times out on 4/5 (1 SAT). AND the Full-effort stage is never reached (per-propagation hang).
=> different problem class; needs the queue below, not modular lifting.

## Queue (master reprioritized 2026-05-29)
1. **Per-propagation hang fix FIRST** (prerequisite). Full-effort never reached on Certora because
   Standard cb_propagate is too heavy. Re-profile with ARITH_STAGE_PROF (added — ZOLVER_SELFPROF
   not in this tree), then gate/cache the dominating heavy stages (continue the L2 Full-gate pattern).
2. **NIA→BV** for the wrapping mod 2^256. User guidance: work at fixed 256-bit width — values
   under 256 bits are fine; truncate (mod 2^256) whatever exceeds. = the BLAN bit-blaster approach
   (/mnt/d/D_Study/BUAA/projects/BLAN, our bit_blast was ported from it). Candidate → exact-validate
   (invariant 1). BLAN-static = 3rd oracle.

## Profiler / diag (all env-gated, default unchanged; gate held unit 883/883, nia reg 113/113 OFF)
- `ARITH_STAGE_PROF=1` → per-NIA-stage cumulative ms + calls, dumped every 2s to stderr (survives
  timeout-kill). In ArithSolverBase::runReasonerPipeline.
- `SOLVE_PHASE_PROF=1` → coarse phase markers in Solver::checkSatInternal (enter / preprocess-done /
  detect-done / setup-done / atomize-done), flushed.
- `XOLVER_NO_EXPAND_FUNCTIONS=1` → parse with SOMTParser define-fun inlining OFF (diag).

## LEVER #4 RE-DIAGNOSED (2026-05-29) — it is NOT the NIA per-propagation hang.
Profiled Certora QF_UFNIA: 14/14 sampled cases hang with **0 [PHASE] lines and 0 STAGE-PROF dumps**
=> the hang is in PARSING, before checkSatInternal / any theory check. CONFIRMED by toggle:
`XOLVER_NO_EXPAND_FUNCTIONS=1` → parse instant, returns `unknown` fast; default (expand ON) → timeout.
ROOT: Solver.cpp:538 sets SOMTParser `expand_functions=true` → parse-time define-fun INLINING. The
Certora files have many cross-referencing define-funs (x97/x69/x60…) over ite + 2^256; expansion is
super-linear (applyFunPostOrder memoizes within ONE body, but bodies re-inline across call sites and
nested define-funs compose) → exponential time. z3 parses fine.
=> The Certora EQ+NA medal lane is PARSER-bound, not NIA-bound. (The old per-propagation finding in
[[project_nia_perpropagation_perf]] was a DIFFERENT subset/branch that did reach NIA; this sample
never does.) FIX = frontend/SOMTParser (A5 lane / submodule): either (a) cross-call-site memoized /
hash-consed expansion in SOMTParser, or (b) parse with expand OFF + expand define-fun apply nodes in
our hash-consed CoreIr. High blast radius (all logics) → dispatch decision needed. NIA→BV (lever #5)
also needs this first (everything needs parsing).
