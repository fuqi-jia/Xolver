# NOTES-eqna — EQ+NA unknown→verdict campaign

Worktree `../zolver-eqna`, branch `agent/eqna-2` (off `origin/integration`,
tip 735d6df which includes my routing 35137f9+3976de8). Submodules are SYMLINKS
to the main checkout (re-symlink after any `git reset --hard`). Binary:
`build/bin/xolver` (rebuilt 23:43 on integration). Cost is noise (Max plan).

## Task
Convert EQ+NA `unknown` → validated verdicts, case-by-case. Logics:
QF_UFNIA / UFNRA / UFDTNIA / ANIA / AUFNIA.
1. Inventory: Xolver vs z3+cvc5; find `recoverable` (xolver=unknown, oracle
   definite) and `recoverable-slow` (xolver timeout/err, oracle definite).
2. Trace + classify each → table below.
3. Fix my-lane causes → validated verdict. Gate: default-OFF + unknown
   guardrail, model-validate every SAT, comb reg OFF+ON, 0-unsound, push per fix.

## Tooling
`python3 -m eval.compare --root /mnt/d/.../NLColver/benchmark/non-incremental
  --logic <L> --solver build/bin/xolver --timeout <s>
  --flags XOLVER_COMB_ARRAY_NIA=1 -j 2 --json-out NOTES/inv_<L>.json`
Classes: correct / UNSOUND / recoverable / recoverable-slow / other.

## Classification buckets (root cause → action)
- combination-routing (MY lane) → fix
- model-extraction floor / strict-validation downgrade (MY lane, uflra_007 a=b
  class) → recover if model genuinely valid
- EUF / array / DT incompleteness (MY lane) → add completion axiom
- NIA / NRA-engine timeout (NOT my lane) → route to NIA/NRA agent with trace

## Established facts
- QF_ANIA/AUFNIA: routing DONE; cases route-then-timeout = NIA-engine-bound
  (NiaSolver.cpp:237 opposite-polarity `pendingUnknown_` floor). Recovery there
  needs the NIA engine, not routing. `XOLVER_COMB_ARRAY_NIA` promotion gated on
  NIA closing within budget (24s tradeoff).

## Tooling UPDATE (integration changed the harness)
- `eval.compare` is now baseline-vs-candidate differ, NOT an inventory runner.
- Inventory = `tools/run_benchmark.py --logic <L> --compare-with z3
  --benchmark-dir /mnt/d/.../NLColver/benchmark/non-incremental
  --oracle-cache NOTES/oracle_<L>.json -j2 -t12` (set env XOLVER_COMB_ARRAY_NIA=1).
  Output → benchmark_results/<run>/<L>/statistics.json (per-case results[]).
- Parse with `python3 NOTES/inv_parse.py <statistics.json>` → recoverable /
  recoverable-slow / UNSOUND buckets.

## Inventory results
### QF_UFNRA (58 cases) — DONE 2026-05-29
correct=9 recoverable=14 recoverable-slow=27 UNSOUND=0 other=8 (8=z3 also t/o).
- **14 recoverable = `20230328-sqrtmodinv-hoenicke/` family, instant unknown
  (0.0-0.1s)**. Root cause: `[ATOM] unsupported NRA/NIA kind=24` (Leq). The
  atom contains REAL DIVISION BY A VARIABLE (`(/ 1.0 s)` from axiom_frac_bound);
  PolynomialConverter returns nullopt for non-constant denominator
  (PolynomialConverter.cpp:174) → atomizer rejects atom → unknown.
  Term-ite (Real) is already supported (verified). Division is the SOLE blocker.
  → MY LANE: capability gap (frontend/atomization). FIX = RealDivLowerer (below).
- 27 recoverable-slow = `cas/` family + a few: xolver timeout @12s, z3 definite.
  → NRA-engine-bound (reach engine, run out of budget). Route to NRA agent.
### QF_AUFNIA (17 cases) — DONE 2026-05-29
correct=0 recoverable=0 recoverable-slow=16 UNSOUND=0 other=1 (z3 also t/o).
All 16 = UltimateAutomizer/* timeout @12s (NOT instant-unknown → they reach the
engine). Confirms established fact: NIA-engine-bound (NiaSolver.cpp:237 floor),
NOT my routing. → ROUTE TO NIA AGENT. No my-lane atomization gap in QF_AUFNIA.
### QF_UFDTNIA (80 cases) — DONE 2026-05-29
correct=1 recoverable=0 recoverable-slow=39 UNSOUND=0 other=40 (z3 also t/o on
many Certora). ALL recoverable-slow = 20230314 Certora/* timeout @12s, NO
instant-unknown → all post-atomize. SAME Certora EVM family as the NIA handoff
(task: profile Certora QF_UFNIA hang). This family spans QF_UFNIA(282)+
QF_UFDTNIA(39) = TOP LEVER. Pivoting to Certora profiling.
### QF_ANIA (157 cases) — DONE 2026-05-29
correct=0 recoverable=25 (20 INSTANT <1s + 5 slow) recoverable-slow=35 UNSOUND=0
other=97. NEW MY-LANE GAP FOUND: 20 instant-unknown (SVCOMP UltimateAutomizer
avg20/floppy2/sum10/lcm2) bailed with `IntDivModLowerer: needsEUF but logic=
QF_ANIA`. Root cause: hasEuf list (Solver.cpp:836) omitted QF_ANIA/QF_AUFNIA,
which DO register an EufSolver under XOLVER_COMB_ARRAY_NIA routing → int
div/mod-by-variable (needs div-by-0 UF) wrongly rejected.
FIX (below): add QF_ANIA/AUFNIA to hasEuf, gated on XOLVER_COMB_ARRAY_NIA. After
fix the 20 cases reach the NIA engine: floppy2→timeout, sum10/avg20→`NIA: pending
unknown (opposite polarity)` = NiaSolver.cpp:237 floor (NIA lane, established).
So fix removes the my-lane bail; verdict closure is now NIA-engine-bound.
### QF_UFNIA (200-case random sample, t=6) — DONE 2026-05-29
correct=40 recoverable=79 recoverable-slow=18 UNSOUND=0 other=63. z3 solves
≳119/200 (~60%) → WINNABLE family, the medal flagship. 73 of 79 recoverable are
"instant" (<1s) — but NOT a my-lane atomization bail: traced 3 (Zohar-alive/
Zohar-ic) all hit `NIA: pending unknown (opposite polarity asserted)` fast.

### VERIFIED DEEP-DIVE: QF_UFNIA Zohar "opposite polarity" floor (instrumented)
Diagnostic in NiaSolver::assertLit (reverted after). Smallest case
int_check_bvsge_bvand_rtl.smt2 (invertibility-condition, pow2/intand/intor as
UNINTERPRETED fns; div/mod by pow2(l)). Trace:
  [A] var=24 sign=1 level=9825   (pos asserted, decision level ~9825!)
  [B] to level=9825 / [B] to 9824 (one-level chronological backtracks)
  [A] var=24 sign=0 level=9824   → OppositePolarity → pendingUnknown (poly atom)
ROOT CAUSE = STRUCTURAL SAT BLOWUP, not a routing bug:
- Decision level reaches ~9825 with one-level-at-a-time backtracks (…9708→9707…):
  the formula expands (every define-fun inlined: pow2/bitof/intmod/intudiv… +
  div/mod-by-pow2(UF) lowering + nonlinear atomization) into THOUSANDS of SAT
  vars → degenerate deep chronological search.
- The opposite-polarity floor (ActiveLiteralSet, NiaSolver.cpp:171) is a SOUND
  symptom of this deep search (var flips after a backtrack the theory state
  hasn't fully cleared at that depth), not the disease. Latches → fast unknown.
- It is BENIGN/helpful: without it the search times out anyway (12s unknown).
  Fixing the bail = 0.1s-unknown → 12s-unknown, no score gain, worse wall-clock.
CLASSIFICATION: structural (formula blowup + degenerate SAT search). Winnable
only via z3/cvc5-style bit-width-independent reasoning (the Niemetz/Preiner/
Reynolds/Zohar/Barrett/Tinelli CADE-27 invertibility method) — a major NIA/
preprocessing redesign, NOT a quick my-lane fix. FRONTIER, route/document.
REALITY CHECK: z3 wins ~60% of QF_UFNIA but via specialized reasoning; our NIA
engine structurally can't. The 2 my-lane gaps (real-div, hasEuf) are the
closeable ones; the rest of EQ+NA is NIA-engine/structural-bound.

## OVERALL EQ+NA PICTURE (inventory complete, 2026-05-29)
| logic | my-lane gap | status |
|-------|-------------|--------|
| QF_UFNRA | real div-by-var | FIXED (RealDivLowerer) → NRA-engine-bound |
| QF_ANIA | IntDivMod hasEuf | FIXED → NIA-floor-bound |
| QF_AUFNIA | none | NIA-engine-bound (route NIA) |
| QF_UFDTNIA | none | NIA divisors-hang (cap → NIA) |
| QF_UFNIA | none | NIA divisors-hang (Certora) + structural blowup (Zohar) |
My-lane atomization/routing gaps CLOSED. Remaining = NIA-engine + structural.

### hoenicke QF_UFNRA spin (post-RealDivLowerer) — CLASSIFIED, NRA lane
gdb-sampled modSimpleTest (3x): 100% inside CdcacCore::solveLevel (deep
recursion) → checkFullSample → LibpolyBackend::signAtRational →
LibPolyKernel::sgnVarId. The "repeated identical 3-constraint CDCAC-FULL" I
saw earlier is the NRA engine's internal CAD cell lifting, NOT a combination
loop. NRA-engine-bound (CdcacCore), NOT my lane. → ROUTE TO NRA AGENT.

## Fixes shipped / in progress (cont.)
- **IntDivModLowerer hasEuf for QF_ANIA/AUFNIA (verifying)**: Solver.cpp, rides
  existing XOLVER_COMB_ARRAY_NIA gate (no new flag). Removes false needsEUF bail
  for the array+NIA stack (which has EUF). 20 QF_ANIA instant-unknowns now reach
  NIA engine. SAT covered by default-on niaSatFloor (nonlinear&&!realVar). Gates:
  reg 661/661 OFF; QF_ANIA re-run mismatch-check in progress.

## Certora EVM hang investigation (NIA handoff, task #3)
Smallest case: QF_UFNIA/20230314-Jaroslav-Bendik-Certora/
72658_63104dadde9c6026353f_70_QF_UFNIA.smt2 (12.9KB, 80 asserts, 22 mod 2^256,
93 declare-fun, 4 ite). mod-by-const 2^256 lowers to LINEAR q*2^256+r.

### VERIFIED PROFILE (gdb-SIGINT, 3 samples) — CONTRADICTS the NIA handoff
The handoff claimed "zero NiaSolver activity, hang is combination/EUF/SAT". FALSE
(3rd wrong diagnosis on this case). gdb backtrace, all samples, worker thread:
  __gmpn_divrem_1 / __gmpn_tdiv_qr  (GMP trial division)
   ← UnivariateIntegerReasoner::divisors(mpz)              [the hang]
   ← UnivariateIntegerReasoner::findIntegerRoots()
   ← NiaSolver::stageUnivariate()
   ← ArithSolverBase::runReasonerPipeline → check
   ← TheoryManager::check ← CadicalTheoryPropagator::cb_propagate ← CaDiCaL
Main thread is just pthread_join-waiting on the worker. The hang IS the NIA
pipeline: `divisors()` (UnivariateIntegerReasoner.cpp:11) trial-divides up to
sqrt(|a0|) — for a 2^256 constant term that's ~2^128 bignum modulos = effective
hang. NOT combination/EUF/SAT. NOT my lane (NiaSolver/UnivariateIntegerReasoner).

### Classification
- PERF bottleneck, FIX ALREADY EXISTS: `XOLVER_NIA_DIVISOR_CAP` (default-OFF,
  UnivariateIntegerReasoner.cpp:36, bails to Incomplete when |a0|>10^12). VERIFIED:
  cap OFF → hang(timeout); cap ON → sound `unknown` in 251ms. NIA should promote.
- STRUCTURAL (hard) to SOLVE: even hang-free (cap ON), the smallest Certora case
  stays `unknown` under every NIA model-finding path tried —
  +BITBLAST / +ICP / +MODULAR / +LOCALSEARCH all → unknown (15-20s). z3=sat on
  this one but z3 is 4/5 timeout on Certora overall ⇒ mostly hard-for-everyone.
- SCORE REALITY: divisor-cap is HYGIENE not a medal lever (hang=timeout=unknown=0
  per-case). The win requires NIA model-construction for EVM mod-2^256 SAT — open
  frontier, low ROI (z3 also mostly t/o). Do NOT over-invest the EQ+NA budget here.

### HANDBACK TO NIA AGENT (verified, actionable)
1. Promote XOLVER_NIA_DIVISOR_CAP default-ON: removes the hang across 282 QF_UFNIA
   + 39 QF_UFDTNIA Certora cases (1200s waste → 251ms unknown). Sound (Incomplete
   never read as UNSAT). Already implemented + gated.
2. EVM mod-2^256 SAT model-finding is the real (hard) lever; bitblast/ICP/modular
   do not close the smallest case. Frontier, not quick win.

## Trace + classify table
| case | logic | xolver | oracle | root cause | bucket | action |
|------|-------|--------|--------|-----------|--------|--------|
| sqrtmodinv-hoenicke/* (14) | QF_UFNRA | unknown(0.0s) | sat/unsat | real `/` by var → atom rejected | atomization capability | FIX RealDivLowerer |
| cas/* (~25) | QF_UFNRA | timeout | sat/unsat | NRA engine budget | NRA-engine | route to NRA agent |

## Fixes shipped / in progress
- **RealDivLowerer (SHIPPED 9e41e83, pushed agent/eqna-2)**: gates unit 895/895,
  reg 661/661 OFF + 187/187 ON, 0 unsound. div-by-0 corner ON→unknown (z3=unsat).
  hoenicke family now reaches CDCAC (no longer instant-unknown) but engine/combo
  loop times out (z3 0.02s) → NRA-engine-bound, ROUTE TO NRA AGENT. The combo
  layer re-checks an identical 3-constraint set (CDCAC-FULL spin); could be NRA
  perf OR a combination arrangement non-convergence — flagged for NRA agent.
- **RealDivLowerer (orig design note)**: new preprocess pass purifies real `/` by a
  non-constant denominator into fresh `q` + guarded def
  `(=> (not (= b 0)) (= (* q b) a))`. Flag `XOLVER_REAL_DIV_PURIFY` default-OFF,
  gated to logics containing NRA/NIRA. Files:
  src/frontend/preprocess/RealDivLowerer.{h,cpp}, wired in Solver.cpp after
  UfInArithPurifier; unit test tests/unit/test_real_div_lowerer.cpp.
  Soundness: guard preserves SMT-LIB div-by-0 (q free when b=0); every model
  extends → no false-UNSAT; div-by-0 functional-consistency corner caught by
  SAT model-validation floor. Hand-encoded minimal case → sat (verified).
