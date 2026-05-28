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

### Fix attempt 1 (FAILED) — applyFun memoization
Added a global memo on `Parser::applyFun` keyed by (funcDef ptr, param ptrs) +
keep-alive (base_parser.cpp; parser.h). Semantics-preserving. Built OK. RESULT:
Certora still TIMEOUT(ph=0) on all 8 sampled => INSUFFICIENT. Why: the blowup is
compositional inlining with DISTINCT args (wrap-fns applied to many different
subexprs), so same-(def,args) memoization rarely hits. NOT pushed to SOMTParser
main (it's not the fix; left in the worktree copy only).
### Real cause + real fix
SOMTParser eagerly FULLY-EXPANDS define-fun bodies (no global hash-consing), so
stored/expanded bodies grow exponentially down the define-fun dependency chain.
z3 parses fine because it keeps macros / hash-conses. REAL FIX (architectural,
pick one): (a) global hash-consing in the node factory (getNodeManager/createNode
/mkOper) so identical subterms share — benefits ALL parsing; (b) lazy define-fun
expansion (don't inline at definition; expand at use with sharing); (c) STOPGAP:
expansion node-count cap → abort to fast `unknown` (sound, frees the time budget
vs a 1200s hang) — small, unblocks but doesn't solve. All are frontend/parser,
shared infra. Awaiting master's depth call.

### CORRECTION (2026-05-29) — hash-consing IS present; "global hash-consing" is MOOT.
NodeManager::createNode → insertNodeToBucket dedups (hashCode + isEquivalentTo).
So SOMTParser is already globally hash-consed. The blowup is NOT missing sharing
— it's EAGER FULL define-fun expansion of COMPOSITIONAL define-funs with DISTINCT
args. Confirmed: 72658 (smallest, 247 lines) has 25 define-funs that compose
(x2 → x72/x45/x111 → x40, each calling x40 with DIFFERENT args x4*x4 / x4*0 /
0*x4 / x4*(2^256-1)); distinct args ⇒ distinct expanded nodes ⇒ dedup can't help
⇒ multiplicative growth down the chain ⇒ exponential. Parse never finishes in
146s; z3 parses instantly because it keeps define-funs as MACROS (lazy, never
fully expands). My applyFun memo (keyed by def+args) can't help (args distinct);
REVERTED to keep SOMTParser pristine.
REAL FIX = LAZY define-fun handling (keep macros; do NOT eagerly inline at parse;
expand on-demand / never fully) — a substantial frontend+SOMTParser+CoreIr
architecture change. AND the Certora lane is hard for z3 (4/5 timeout). => LOW ROI.
RECOMMEND: deprioritize the Certora parser rewrite; quantify the shipped broad
QF_NIA levers (modular L3+Hensel, WalkSAT SLS) via E's differential instead.
