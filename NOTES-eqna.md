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
- TODO: QF_ANIA (157, est. NIA-bound), QF_UFNIA full (806 — Certora subset profiled via handoff).

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
