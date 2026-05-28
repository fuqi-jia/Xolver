# NOTES-nia (Agent NIA, branch agent/nia-2)

Running notes. Branch `agent/nia-2` (integrated main + my work). Commit+push per lever.
Gates every lever: default-OFF flag, 0-unsound, nia reg 113/113 OFF+ON, self-measure via eval/.

## Shipped (verified + pushed) — on agent/nia-2
- **--parse-only** CLI mode (aa24e72): parse + print `parse-ok` + exit; lets E tag
  parse-vs-solve failures corpus-wide. (Certora confirmed solve-bound, not parse.)
- **Modular reasoner broadened to non-pow2** (a6945ec, XOLVER_NIA_MODULAR): relaxed
  div-group recognition isPow2(n)->n>=2; enumerate at m=lcm(group n's); extended
  no-group brute set incl. composites. Catches `mod 3/5/10/...` residue
  contradictions. Hensel stays pow2-only. unit 884/884, nia reg 113/113 OFF+ON.

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

## Preliminary local differential (2026-05-29, 110-case family-split QF_NIA sample)
baseline(no flags) vs candidate(XOLVER_NIA_MODULAR=1 XOLVER_NIA_LOCALSEARCH=1), -t15 -j2.
solved 15->29 (+14), unsat 5->19 (+14), sat 10->10 (+0). eval.compare: +14 @1200 AND
@24, 0 wrong, 0 decided-disagreements, promote=YES.
SOUNDNESS of the 14 new-unsats: 8 have ground-truth :status unsat (4 MathProblems
STC_*, 4 sqrtmodinv modInv8/16/64/128); 6 UltimateAutomizer ps* are :status=unknown
with z3+cvc5+BLAN ALL timing out (no oracle) — recovered ONLY by our modular reasoner.
ps4 hand-verified sound in python: goal (3y^2+2y^3+3y^4) mod 4 != 0 is UNSAT because
the poly ≡0 mod4 ∀y; reasoner enumerates y mod4, r=0 always, neq r!=0 always violated.
Same mechanism for the other ps. 0 unsound detected.
=> KEY: the modular reasoner BEATS z3+cvc5+BLAN on STC (MathProblems) + ps
(UltimateAutomizer) — general nonlinear families with an always-true `(poly) mod k`
goal. The modular lever reaches FAR beyond modInv. SLS gave 0 SAT recovery in this
(UNSAT-heavy) sample. NEXT LEVER (data-directed): broaden modular further (more
moduli / structural patterns), it's the dominant UNSAT lever. Sample is UNSAT-biased;
SLS value needs a SAT-rich sample to show (full corpus is ~2:1 SAT:UNSAT for leaders).

## Task 13: per-propagation perf (profiled engine-reaching QF_NIA timeouts)
ARITH_STAGE_PROF on the 65 sample timeouts: nia.presolve is the hot stage
(~1.1s/call dense Dartagnan B_2; normalize+presolve re-run ~8000x/Standard-effort
on mcm 08). SHIPPED L4 XOLVER_NIA_PRESOLVE_FULL (1ba8606, default-OFF): gate
nia.presolve to Full-effort (like univariate/bit-blast). Differential: +6 UNSAT
over MODULAR+LOCALSEARCH (the presolve-bound timeouts reach a verdict at Full).
TOTAL all-3-flags on 110-sample: baseline 15 -> 35 solved (+20, all <=24s, 0
unsound, promote=YES). unit 884/884, nia reg 113/113 OFF + all-3-ON.
SOUNDNESS of +20: 8 ground-truth :status unsat (STC+modInv); 12 :status unknown
(ps/egcd/hard UltimateAutomizer-style) where z3+cvc5+BLAN all timeout — sound by
construction (modular invariant-7 + established presolve HNF/FM), ps4 hand-verified.
NOTE: 2019-ezsmt timeouts are NOT engine-bound (no STAGE-PROF dump) — likely
SAT-search; SLS/value-selection territory, needs a SAT-rich sample to measure.

## Task 14 (NIA->BV) = MOOT (data-directed dead-end, documented per master's rule)
Profiled the remaining 57 timeouts: bit-blast ALREADY fires on the bounded ones
(AProVE aproveSMT*: nia.bit-blast ms=7229; calypto problem-*: ms=5918) — it's SLOW,
not absent. So "add NIA->BV for bounded NIA" is moot; the blaster exists + runs
Full-effort by default. The remaining gap splits: (a) bit-blast-SLOW (AProVE/calypto
— optimize the existing blaster, big); (b) SAT-search-bound (2019-ezsmt, UltimateAutomizer
hard — NO dominant engine stage). Confirmed ezsmt are SAT (z3@60s=sat; we timeout@15s,
WalkSAT too weak) => SAT gap is REAL. (c) residual presolve (mcm/Dartagnan per-call).
=> NEXT LEVER (data-directed) = DEEPEN WalkSAT SLS for the SAT gap (bigger Full-effort
budget + restarts + feasible-jump moves) — task-12 SAT branch, now justified. But it's
substantial; per master "reprioritize on E's panda authoritatively" — E's full differential
confirms SAT-gap corpus-wide magnitude before heavy SLS investment. Task 14 skipped, not built.

## Soundness hardening of oracle-blind modular UNSATs (priority-1, DONE 2026-05-29)
The 12 oracle-blind modular UNSATs (z3/cvc5/BLAN all timeout) are the medal win AND
the soundness exposure — nothing external can catch a false-UNSAT there. Hardened:
- **Brute-force certificate FLOOR** (f7689f4): before emitting any enumeration-path
  modular UNSAT, independently brute-force ALL vars over Z/m (fresh, no
  substitution/closure/Hensel reuse) over the raw constraints. ConfirmedUnsat->emit;
  FoundModel->FLOOR (plan bug caught, never emit false UNSAT); OverBudget->emit
  (large-m structured: modInv via Hensel / :status-unsat-confirmed). Default-ON
  within XOLVER_NIA_MODULAR. So every small-m oracle-blind UNSAT is cert-backed.
- **Graded-ladder** (6af3fc3, tests/modular_ladder/): 5 isolated small-k
  always-true-mod-k instances. z3 DECIDES L1/L3/L5 and AGREES unsat with our engine
  (mod-k reasoning validated on z3-checkable); z3 can't decide L2/L4 (oracle-blind
  regime) where engine + brute-cert=ConfirmedUnsat, python-confirmed. Same code path
  => real oracle-blind ps/STC inherit confidence.
- **CRT coprime pass** (908fe6e, priority-2): also try mod 3/5/7 coprime to the group
  base; cert-floored. No local gain on the sample, broader corpus coverage.
Net: oracle-blind modular UNSATs are cert-backed + ladder-validated => safe toward
all-on final. unit 884/884, nia reg 113/113 OFF + all-3-flags, 0-unsound throughout.

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

### CORRECTION 2 (2026-05-29) — "parser-bound" was a -v / cerr-silencing ARTIFACT.
The CLI silences stderr unless `-v` (Solver.cpp:157 → NullStreambuf). My Certora
phase/stage profiling runs OMITTED `-v`, so [PHASE]/STAGE-PROF (cerr) were
SUPPRESSED — I misread "0 lines" as "hang before checkSatInternal = parser."
WRONG. Re-run WITH `-v`: ALL phases print in ~20ms: enter(asserts=80) →
preprocess-done(307) → detect-done(307) → setup-done(357) → atomize-done(357).
So PARSE + lowering + atomization are FAST (~20ms). `--parse-only` (stdout, not
silenced) confirms parse-ok fast too. The hang is in SOLVING (after atomize), and
ARITH_STAGE_PROF shows NO NiaSolver-pipeline dumps in 15s ⇒ the NIA arith pipeline
is NOT the hot path here ⇒ the hang is in the COMBINATION/EUF/SAT layer
(TheoryManager / SharedEqualityManager N-O diseq / CaDiCaL search / propagator) —
A3's lane — consistent with the ORIGINAL [[project_nia_perpropagation_perf]]
(NIA/combination-engine-bound, NOT parser). The whole "eager define-fun expansion
/ lazy-macro" thread is MOOT (parse is fast). SOMTParser untouched/pristine.
--parse-only tool is still useful: lets E confirm parse-phase is fine corpus-wide.
NEXT: localize the solve hang (SAT vs EUF vs combination N-O) — coordinate w/ A3.
LESSON: always pass `-v` when reading cerr diagnostics from the CLI.
