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
- TODO: QF_AUFNIA (17), QF_UFDTNIA (80), QF_ANIA (157), QF_UFNIA (806, sample).

## Trace + classify table
| case | logic | xolver | oracle | root cause | bucket | action |
|------|-------|--------|--------|-----------|--------|--------|
| sqrtmodinv-hoenicke/* (14) | QF_UFNRA | unknown(0.0s) | sat/unsat | real `/` by var → atom rejected | atomization capability | FIX RealDivLowerer |
| cas/* (~25) | QF_UFNRA | timeout | sat/unsat | NRA engine budget | NRA-engine | route to NRA agent |

## Fixes shipped / in progress
- **RealDivLowerer (IN PROGRESS)**: new preprocess pass purifies real `/` by a
  non-constant denominator into fresh `q` + guarded def
  `(=> (not (= b 0)) (= (* q b) a))`. Flag `XOLVER_REAL_DIV_PURIFY` default-OFF,
  gated to logics containing NRA/NIRA. Files:
  src/frontend/preprocess/RealDivLowerer.{h,cpp}, wired in Solver.cpp after
  UfInArithPurifier; unit test tests/unit/test_real_div_lowerer.cpp.
  Soundness: guard preserves SMT-LIB div-by-0 (q free when b=0); every model
  extends → no false-UNSAT; div-by-0 functional-consistency corner caught by
  SAT model-validation floor. Hand-encoded minimal case → sat (verified).
