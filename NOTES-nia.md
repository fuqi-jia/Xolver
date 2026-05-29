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

## Bit-blast perf lever (2026-05-29, master unheld it; SLS stays held for E)
Profiled (NIA_BITBLAST_PROF, encode-vs-SAT split) the ~7s on AProVE/calypto:
- (a) encode-bound + ALWAYS-OVERFLOW (aprove2313): 5s encode, sat_ms=0, 200k-var
  budget hit every attempt, re-solved ~10x across Full checks => futile Unknown.
- (b) SAT-SOLVING-dominated (aprove2593/3390): encode ~2s, SAT 6-8s growing,
  62k/43k satvars, ONE long solve. Encoding already BLAN-optimized.
SHIPPED: bit-blast result cache XOLVER_NIA_BITBLAST_FAST (026417c, default-OFF),
memoize solve() by (cs polys+rels, domain bounds). VERDICT-PRESERVING (nia bucket
113 cases, 0 verdict-diffs OFF vs ON; unit 9/9). HONEST: 0 newly-solved on the
13-case AProVE/calypto subset — the dominant cost is ONE long SAT solve of the
wide CNF, NOT redundant repetition, so the cache (and collapsing futile
re-encoding) doesn't cross the 18s timeout. Cache kept as safe gated building block.
=> REAL recovery lever = faster SAT: incremental solver reuse across width attempts
(warm-start, no re-encode) and/or smaller CNF. Bigger + verdict-preservation-
sensitive (width changes are NOT verdict-preserving; incremental SAT IS if same
widths). Flagged for master: invest in incremental-SAT, or hand bit-blast-recovery
magnitude to E's panda. Tighter-width growth ruled out (changes verdicts -> fails gate).

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

## LEVER — RRT divisor enumeration via prime factorization (2026-05-29)
Flag XOLVER_NIA_DIVISOR_FACTOR (default-OFF). Replaces the O(sqrt|a0|) trial
division in UnivariateIntegerReasoner's RRT divisor enumeration with
prime-factorization enumeration. RRT: every integer root divides the constant
term a0, so the root search must enumerate ALL divisors of a0 — trial division to
sqrt(|a0|) is ~2^128 iterations for an EVM mod-2^256 constant (effective hang;
previously only the XOLVER_NIA_DIVISOR_CAP bailed it to unknown). Factorization of
2^256 = {2:256} extracts in 256 `%2` steps -> 257 divisors enumerated instantly,
so RRT now RUNS TO COMPLETION (solves) where the cap could only give unknown.

Files: UnivariateIntegerReasoner.{h,cpp} — new static `completeDivisors(n,&complete)`
(public for testing) unifies both divisor sites in findIntegerRoots:
  - factor mode: primeFactorizeBounded (trial-divide primes up to B=10^6) +
    divisorsFromFactors (cartesian product of prime-power ranges, capped at 1000
    divisors). complete=false => caller -> IntegerRootStatus::Incomplete -> unknown.
  - default mode: original O(sqrt n) trial division behind divisorEnumerationInfeasible.
SOUNDNESS (invariant 7 — never UNSAT from incomplete reasoning): complete=true IFF
the FULL divisor set was enumerated. Two bail conditions keep this exact:
  1. Residual cofactor with no factor <= B: accepted as prime ONLY when m <= B^2
     (a composite < B^2 MUST have a factor < B, which the loop found => deterministic
     primality, NOT probabilistic). m > B^2 => complete=false (DELIBERATELY no
     Miller-Rabin: a false "probable prime" would under-enumerate divisors and could
     fabricate a false UNSAT; the target corpus is pure powers of 2 so this costs
     nothing). 2. Divisor count > 1000 => complete=false. Incomplete is never read
     as UNSAT (run() derives Conflict only on Complete && empty roots).
Gate: unit 890/890 (+6 new test_univariate_divisors.cpp: full-enum, factor==default
on small composites, 2^256 completes + contains 2^128, large-semiprime incomplete,
over-cap incomplete, single-large-prime accepted). nia reg 113/113 OFF + ON,
0-unsound. Synthetic x^2=2^256/2^255 cases are caught earlier (square-rule), so the
corpus win is unknown->solved on cases the cap previously floored, not new
sat/unsat on micro-tests. Pushed origin/agent/nia-2.
This EXHAUSTS the data-independent NIA levers -> await-E state (BLAN false-UNSAT
join #16 = immediate #1 if any modular Xolver=unsat & BLAN=sat; E differential picks
SLS vs incremental-SAT, both held).

## SOUNDNESS FIX — false-UNSAT from dropped exclusion reasons (2026-05-29) [f58ed43]
Found by self-served BLAN+z3 differential (master dispatched "study cases BLAN
solves but we time out"). Sampled 150 BLAN-sat QF_NIA, ran full binary (all NIA
levers on): 109 timeout, 19 sat, **18 unsat**. z3 cross-check: 17/18 z3=sat (18th
z3-timeout) => GENUINE false-UNSAT (invariant-7 violation, two oracles agree sat).

Bisect (drop one flag at a time): XOLVER_NIA_PRESOLVE_FULL is the trigger. But it
does NOT change presolve logic — only schedules nia.presolve Full-effort-only. The
DEFAULT path TIMES OUT (per-propagation presolve pathology) and never reaches the
buggy conclusion => "perf unmasks soundness" ([[feedback_perf_unmasks_soundness]]).
ARITH_STAGE_DIAG named the stage: `nia.domain` (stageDomainInference), conflict via
`isEmpty after linearDomain_.run`. NIA_DOM_DIAG: emptied var=global_invc1_0, domain
{0} (finite set, lower=upper=0, all reason satVar 4), value 0 EXCLUDED (nExcluded=1).

ROOT CAUSE: DomainStore::collectEmptyReasons, the "finite set has no valid value"
branch, added lower.reasons+upper.reasons+finiteSetReasons but DROPPED the per-value
EXCLUSION reasons when a member was killed by excludeValue (x!=v) not a bound. So
the conflict clause was {atom4} ("x in {0}") instead of {atom4, exclusion}
("x in {0}" AND "x!=0") — an over-strong learned clause (atom4 globally false) that
pruned a satisfying assignment => false UNSAT. (Matched the observed lits=`4 4 4`.)

FIX (DomainStore.cpp, default-path, NOT flag-gated): attribute the SPECIFIC killer
per finite-set member — exclusion reasons if excluded, bound reasons only if
actually out of range. A weaker+correct conflict clause is strictly more sound
(never over-prunes). Verified: 18 former false-UNSAT -> unsat=0 (16 honest timeout,
2 recovered to z3-agreeing sat). Re-ran the 150 sample post-fix: 0 unsat, sat 19->22
(+3 recovered), 127 timeout, 1 unknown. Plus a FRESH non-overlapping 272-case
BLAN-sat sample post-fix: 0 unsat, 39 sat, 232 timeout, 1 unknown. => across 422
sampled BLAN-sat cases, ZERO false-UNSAT remain (no other unsound conflict path
surfaced). unit 890/890, nia reg 113/113 OFF+ON, 0-unsound. DEFAULT-PATH soundness
fix => master should run full panda differential.
NOTE: remaining ~85% of BLAN-sat are honest timeouts (hard VeryMax/termination
bilinear-Farkas SAT that BLAN's full ICP+eq+blaster+cdcl_t engine solves; our
bit-blast is gated Full-effort + the big boolean structure thrashes before reaching
it) — that's the recovery lever (#24-26), distinct from this soundness fix.

## RECOVERY DIAGNOSIS — why we time out on BLAN-fast-sat cases (2026-05-29) [#24-26]
359/422 sampled BLAN-sat cases time out in Xolver; some BLAN solves in 0.05-0.6s.
Traced 5 (AProVE/calypto/leipzig/ezsmt/VeryMax-ITS) with ARITH_STAGE_PROF + a new
NIA_BITBLAST_DIAG (per-width attempt kind, added to BitBlastSolver.cpp).

WHERE THE TIME GOES (case 1 AProVE, BLAN 0.05s): nia.cdcac ms=8194 calls=1 (CDCAC
churns 8.2s on a SAT case — it's the UNSAT lever, futile here), nia.bit-blast
ms=624 calls=1 -> Unknown. case 2 calypto: presolve 5s + cdcac 2.9s + bit-blast 1.8s
+ local-search 1.1s, all spread across 6 Full-effort checks.

WHY BIT-BLAST FAILS (the core divergence, NOT an encoding bug):
- NIA_BITBLAST_DIAG on AProVE: UNSAT at EVERY width K=2..32 (vars 4105..280270), even
  though a {0,1} model exists (b__15=0 collapses all degree-3 terms; verified by hand
  + z3). Box is incomplete (unbounded vars) so this UNSAT is correctly downgraded to
  Unknown (SOUND) — but it can't find the model.
- Minimal-construct tests (products, deg-3, neg-coeff nested products, not(and(=)))
  ALL solve correctly. The blaster is NOT broken.
- DECISIVE: pin the disequality branch (replace `not(and E1 E2 E3)` with `not E1`)
  and feed the full conjunction -> bit-blast finds SAT INSTANTLY at K=2 (valid+inBox).
  => the blaster encoding is CORRECT; the problem is INTEGRATION: our nia.bit-blast
  only blasts the CURRENT CDCL(T) assignment's theory atoms (normalized_), NOT the
  whole formula's boolean structure. For boolean-rich formulas the outer SAT solver
  commits a non-satisfying disequality resolution, bit-blast returns Unknown (no
  conflict -> no backtrack signal for an incomplete box), the loop stalls -> unknown.
- BLAN bit-blasts the WHOLE formula (boolean + arithmetic) into ONE SAT instance, so
  the disjunctions and the arithmetic are searched together -> 0.05s.

SLS CHECK (built WalkSAT, XOLVER_NIA_LOCALSEARCH, big budget 8s/20s, bit-blast off):
recovers only 1/5 (AProVE). Not robust for these.

DECISION (master reserved SLS-vs-bit-blast; data resolves it): bit-blast is the RIGHT
tool but needs WHOLE-FORMULA eager blasting (translate the entire QF_NIA formula —
Int vars -> bit vectors, every arith atom -> bit-level clauses, boolean skeleton ->
CNF — into one SAT solve, like BLAN), NOT the current per-assignment Full-effort
stage. SLS is too weak (1/5). This is a sizeable NEW capability (a portfolio
int-blast mode wired to the SAT core / a frontend int-blast pass), not a tweak and
not "wire up built machinery" — recommend to master before building (overlaps the
held incremental-SAT/whole-blast lane). Per-assignment bit-blast stays as-is.
Cheaper partial win available meanwhile: time-box nia.cdcac so it stops wasting
multi-second budget on SAT cases (doesn't recover these — bit-blast already failed —
but frees budget broadly). Kept NIA_BITBLAST_DIAG (env-gated) for the blast work.

## LEVER — EagerBitBlastSolver: whole-formula eager bit-blast arm (2026-05-29) [GREENLIT]
Master greenlit the whole-formula recovery lever as a SOUND PORTFOLIO ARM. Flag
XOLVER_NIA_EAGER_BITBLAST (default-OFF). NEW files src/theory/arith/bit_blast/
EagerBitBlastSolver.{h,cpp}; wired in Solver.cpp checkSatInternal AFTER lowering/
detect, gated to QF_NIA + integer-only, BEFORE TheoryManager setup. On Unknown it
falls through to the CDCL(T) main loop (invariant 5 intact — parallel strategy, not
surgery). NAMING: it's EAGER BIT-BLAST (whole formula -> SAT), NOT "int-blast"
(that term = integer->BV BV-solving; user corrected me).

DESIGN (adapt-to-our-code, not a BLAN 1:1 clone): walk the lowered formula DAG;
boolean skeleton via Tseitin gates (my BitBlastEncoder andGate/orGate/xorGate/
iteGate — already a faithful port of BLAN's logic); each arith atom reified via
enc.relZero(PolyBitBlaster::encodePoly(diff), rel) using PolynomialConverter::
convertConstraint; Int vars -> two's-complement BitVec (width cascade {4,8,16,24,
32}). REUSE: BitBlastEncoder (BLAN-faithful width-growing exact arith add->max+1,
mul->wa+wb) + PolyBitBlaster (Greedy-Addition + CSE = BLAN mkInnerVar).

SOUNDNESS (invariants 1+7): SAT-FINDER ONLY. A SAT model is a CANDIDATE, accepted
only after EXACT integer re-evaluation of EVERY assertion (kernel.evalInteger on
each atom's diff + boolean structure walk). NEVER returns Unsat (bit-blast UNSAT at
a heuristic width proves nothing about the unbounded integer problem -> Unknown).
Any encoding mistake can only downgrade a candidate to Unknown. So sound BY
CONSTRUCTION regardless of encoding subtleties.

TIME-BOX (critical): the arm can't prove UNSAT, so on UNSAT cases it would churn
widths and eat the CDCL(T) budget. Added SatSolver::limit() (CaDiCaL
solver_->limit) -> per-solve conflict cap (XOLVER_NIA_EAGER_BITBLAST_CONFLICTS,
default 50000) + wall-clock budget between widths (XOLVER_NIA_EAGER_BITBLAST_
BUDGET_MS, default 3000) + var budget (_BUDGET, default 20M). Fixed nia_097
timeout->unsat (arm yields, CDCL(T) finishes).

RESULTS (150 BLAN-sat sample, all-on + EAGER_BITBLAST vs all-on baseline):
sat 22 -> 62 (+40 recovered, 27% of sample), timeout 127 -> 62, **0 unsat on
BLAN-sat (sound)**. Per-case: AProVE/leipzig/ezsmt recover at 0.14-0.22s
(BLAN ~0.05s); the rare slow-SAT (>budget) and calypto (needs width>32) miss at
default budget (env-tunable up). Gate: unit 890/890, nia reg 113/113 OFF+ON,
0-unsound. Pushed origin/agent/nia-2.

FLAG HYGIENE this commit (master directive): DELETED superseded XOLVER_NIA_DIVISOR_
CAP (+ divisorEnumerationInfeasible) — DIVISOR_FACTOR supersedes it; CAP was
default-OFF so default behavior unchanged. Live optimization flags stay GATED this
round (differential baseline needs them OFF); master collapses to default after the
differential passes (0-unsound + more solved). One-capability-one-flag going fwd.

KNOWN follow-ups for the eager arm (optimization, not soundness): (1) budget/width
tuning via the differential (3s default misses slow-SAT; calypto needs width>32);
(2) BLAN encoding optimizations not yet ported — offset encoding for bounded vars
(var=lb+t, narrower width), range-splitting, sorting-network addition; CSE is
already ported. Validate-gate keeps all of these sound to add later.

## ENCODING-PARITY WITH BLAN ("对拍", 2026-05-29) — closing the speed gap
Head-to-head on 24 BLAN-sat cases: BLAN 20/24. Xolver eager-arm progression:
11/24 (initial) -> 17/24 (per-var width) -> **18/24 (constant folding)**.
Root-caused via minimal-case SAT-var counts (BLAN prints satVars):
  m_mul (a*b=100): BLAN 231, ours 744->411 (folding).
  m_sum (a+b+..=100): BLAN 159, ours 686->403 (folding).
  1395.smt2: BLAN 25444 vars/1.48s; ours 153k/16.8s -> 98k/8.6s (per-var width)
             -> 60k/3.7s (folding).

FIXES SHIPPED:
1. Per-var width [0a29ca2]: bounded vars at exact width not uniform cascade.
2. **Constant folding in BitBlastEncoder gates [this commit]** — andGate/orGate/
   xorGate/iteGate now short-circuit on constant/(anti)identical inputs instead of
   always allocating a fresh var+clauses. Bit-blasting emits MANY constant inputs
   (padding, sign-extension, zero partial products, LSB carry-in), so this is the
   dominant systematic var reduction (~45% on minimal cases). SHARED ENCODER ->
   benefits BOTH the eager arm AND the per-assignment nia.bit-blast. Exact
   (semantics-preserving): unit 890/890, nia reg 113/113 OFF+ON, 0-unsound.
3. Encode budget guard [a6727bd]: var-budget 2M + in-encode wall-clock check so a
   single huge formula (3110 vars) can't hang the arm.

REMAINING gap to BLAN (still ~1.8-2.5x var count): the bound atoms are still
encoded as adder+comparator (BLAN's OFFSET encoding makes them free) — that's the
next lever. The last 2 unsolved h2h cases are huge formulas (3110 vars) that need
offset to fit. WHY-BLAN-IS-FASTER answer: more compact encoding (constant folding
[now ported] + offset/unsigned vars [next] + tighter operators), not algorithm.

## OFFSET ATTEMPT + POLARITY FIX + COMPLEMENTARITY (2026-05-29, cont.)
1. POLARITY BUG FOUND+FIXED [ce9181e]: per-var bound extraction was polarity-blind
   — it pulled a bound from EVERY simple atom incl. ones under (not ...)/(or ...).
   `(not (= rfc0 0))` made it extract `rfc0=0` and size rfc0 to 1 bit (wrong; real
   constraint is rfc0!=0). Worked only by luck (1-bit signed range held a non-zero
   value). FIX: markTop pass — descend from assertion roots through And ONLY;
   bounds come exclusively from top-level positive conjuncts. Correct by
   construction; validate-gate remains the backstop. (This is the kind of latent
   bug the offset work surfaced.)
2. OFFSET ENCODING ATTEMPTED + REVERTED: value = lb + t (t unsigned in [0,range]),
   skip bound atoms (free). Worked on minimal cases (m_mul 411->377, m_sum 403->318)
   but produced INVALID candidates on full bilinear formulas (1395): exact-encoding
   mismatch on offset-var * unbounded-var products (validate-gate caught it => sound
   Unknown, no recovery). Root cause not fully isolated (the add-result value bitvec
   interacting with PolyBitBlaster products). Reverted to per-var EXACT width +
   polarity-correct bounds. Offset needs more careful work before it helps; the
   bound-atom-skip win is real for the huge 3110-var cases but the product encoding
   must be debugged first.
3. COMPLEMENTARITY CONFIRMED ("exceed BLAN" thesis): same all-flags-on binary —
   modInv8 -> UNSAT (via nia.modular; eager arm bails, reasoning proves it) AND
   1395 -> SAT (via eager bit-blast). The eager arm finds SAT, the
   modular/Hensel/CDCAC levers prove UNSAT, they don't interfere (eager runs first,
   Unknown -> CDCL(T) reasoning). So Xolver = BLAN's SAT power + UNSAT reasoning
   BLAN (a pure bit-blaster) lacks => total > BLAN on the union.

CURRENT STANDING: head-to-head 17-18/24 (BLAN 20), within timing noise. All sound:
unit 890/890, nia reg 113/113 OFF+ON, 0-unsound. NEXT for full parity (20+):
debug+reland offset product encoding, or sorting-network addition.
