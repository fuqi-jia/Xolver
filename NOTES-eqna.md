# NOTES-eqna — EQ+NA unknown→verdict campaign

## ★★ NEW LANE (2026-05-29): cross-division capability audit (EUF/array/combination/DT)
Mission: raise my solvers across the ~12 divisions they serve. The PURE divisions
(QF_UF/AX/ALIA/AUFLIA/UFLIA/UFLRA/DT/UFDT) are NOT NIA/NRA-bound — the bottleneck
there is MY solvers. Data-first audit (family-split sample @24s, ulimit -v 3000000,
-j2, foreground) → fix highest-leverage my-lane gaps → entry-readiness evidence.
Tooling: `eval.select --per-family-cap K --val-fraction 0.5` (cat train+val =
family-balanced sample) → `tools/run_benchmark.py --file-list --compare-with z3
--oracle-cache` → `NOTES/inv_parse.py`. Oracle binaries: z3 + cvc5 both present.

### AUDIT RESULTS (family-split samples vs z3)
| logic | sample | xolver solved | z3 | unsound | top loss family | gap class |
|-------|--------|--------------|----|---------| ---------------|-----------|
| QF_AX | 76 | 41 (54%) | 76 | **0** | storeinv (~all unk), storecomm, swap | array completeness (missed-axiom floor) |
| QF_UF | 99 | 55 (56%) | 98 | **0** | eq_diamond 12, NEQ 11, PEQ 11, SEQ 5 (all TIMEOUT) | EUF perf (cc + SAT-search on transitivity diamonds) |

**QF_UF deep-dive (task #10, EUF perf):** 0-unsound, 55/99. ALL 44 losses are
TIMEOUTS (zero unknown) → PERFORMANCE, not incompleteness. Concentrated in the
synthetic equality-stress families eq_diamond/NEQ/PEQ/SEQ (Strichman-Rozanov
"minimum transitivity constraints for equality logic"). eq_diamond1 (trivial
`(not (= x0 x0))`) solves instantly; the sampled eq_diamond27..96 (95-302 lines)
are real transitivity chains → exponential without good conflict-learning /
transitivity-constraint generation. DEEPER + single-division + riskier than the
array lever. Documented; deferred behind the array fix.

**QF_AX deep-dive (TOP LEVER so far):** 0-unsound, 41/76 solved. The 35 losses
(32 unknown + 3 timeout) ALL hit `array: SAT model violates an original assertion
(missed array axiom instance) — gated to Unknown (sound)` (Solver.cpp:1526). The
EUF/ArrayReasoner theory layer returns SAT before instantiating all needed
read-over-write/extensionality instances; the post-solve ModelValidator catches
the spurious model and the sound floor downgrades to unknown. BOTH directions hit
it: sat cases (model spurious→would be valid with the missing instance) AND unsat
cases (e.g. storeinv_t1: `(= nested-store nested-store) ∧ a1≠a2` → should be UNSAT
but reasoner declares SAT, model violates → unknown).
ROOT CAUSE HYPOTHESIS (ArrayReasoner.cpp:199): the fresh Extensionality witness k
(minted for a1≠a2) is EXCLUDED from `completeStoreSelects` read-indices — so
select(store-tower, k) is never interned, the witness never propagates THROUGH a
positive store-equality hypothesis, and the contradiction/refinement is missed.
Exclusion was a stability choice (witnesses fanning across every array
destabilized storecomm genuine-sats). FIX = include witness k in completion but
BOUND the target arrays to k's own disequality arrays (a1,a2 + towers equated to
them), behind a default-OFF flag. Targets: storeinv + read2/read5 regression;
guard: storecomm must not regress. → task #11.

**FIX IMPLEMENTED (pending build+test): `XOLVER_AX_EXT_WITNESS_COMPLETE`
(default-OFF), ArrayReasoner.{h,cpp}.** The witness k was blocked from completion
by TWO gates: completeStoreSelects skips internalSelect_ (line 194 — Ext's own
select(a,k)/select(b,k) are internal) AND skips extWitnessIdx_ (line 199). So I
capture the interned witness INDEX term id at Ext mint time
(extWitnessIdxTerms_), and under the flag append those to readIdx directly —
completion then reads k across all array terms (store towers included), so Row2
peels select(tower,k) → select(a,k)/select(b,k), congruence on the equal towers
contradicts the Ext disequality → storeinv closes. Bounded (1 witness/diseq pair
× finite arrays, deduped), sound (only tautological selects, never assertions;
model-validation floor stays as backstop).

**★ VERIFIED WIN (2026-05-29):** flag ON converts all sampled storeinv cases
unknown→correct verdict (unsat→unsat, sat→sat, vs z3). **QF_AX slice: 41/76 →
67/76 (+26 solved), MISMATCHES 0, DIFFS 35→9.** Array regression (ax/alia/alra/
auflia/auflra, 33 cases) 33/33 PASS OFF + 33/33 PASS ON. storecomm no-regress
(covered by the slice re-measure). Full reg flag-ON 0-unsound gate: running.
Residual 9 (7 unknown + 2 timeout) = swap-family timeouts + a few harder unknowns
(next slice). Promotion: default-OFF now; server z3-diff QF_AX/ALIA/AUFLIA full
corpus, then default-ON (final = all-on).

## ★ MASTER HANDOFF SUMMARY (2026-05-29, branch agent/eqna-2)
Full EQ+NA inventory done (UFNRA/AUFNIA/UFDTNIA/ANIA + UFNIA sample). **0 unsound
everywhere.** Finding: after my 2 routing fixes, the EQ+NA medal is
**NIA/NRA-engine-bound** — the closeable MY-LANE (atomization/routing) gaps are
closed; remaining unknowns need engine work (not my lane).

SHIPPED (sound, gated, pushed):
1. `9e41e83` RealDivLowerer — real division-by-variable purification (flag
   XOLVER_REAL_DIV_PURIFY, default-OFF, NRA/NIRA logics). Fixes QF_UFNRA hoenicke
   instant-unknown (atomizer kind=24 reject). div-by-0 corner → unknown (sound).
   Gates: unit 895, reg 661 OFF + 187 ON, 0 unsound.
2. `a8b7cc3` IntDivModLowerer hasEuf for QF_ANIA/QF_AUFNIA — the array+NIA stack
   has EUF, so int div/mod-by-var (div-by-0 UF) should not be rejected. Rides
   existing XOLVER_COMB_ARRAY_NIA gate (no new flag). Fixes 20 QF_ANIA SVCOMP
   instant-unknowns. Gates: reg 661 OFF+ON, QF_ANIA 0 unsound.

Both fixes route cases PAST my-lane bails INTO the engine; 0 net solves on the
current corpus today (engine floors) but PREREQUISITE — cases could never solve
while bailing. SAT covered by default-on niaSatFloor / SAT-validation floor.

HANDOFFS (verified diagnoses, not my lane):
- **NIA**: Certora QF_UFNIA/UFDTNIA hang = `UnivariateIntegerReasoner::divisors()`
  trial-dividing sqrt(2^256) (gdb-verified, CONTRADICTS the earlier "not NIA
  pipeline" handoff). Fix EXISTS: promote XOLVER_NIA_DIVISOR_CAP default-ON
  (hang→251ms unknown). Model-finding for EVM mod-2^256 SAT = open frontier.
- **NRA**: QF_UFNRA hoenicke/cas timeouts = CdcacCore::solveLevel CAD recursion
  (gdb-verified), not combination.
- **Structural/frontier**: QF_UFNIA Zohar invertibility = SAT blowup (define-fun
  expansion → ~9800 decision levels) → opposite-polarity floor (benign symptom);
  winnable only via z3-style bit-width-independent reasoning.

PROMOTION ASK: server z3-diff the 2 flags on full QF_UFNRA/ANIA/AUFNIA, then
promote (both default-OFF now; final needs all-on). Local per-logic = 0 unsound.
Full-logic flag-ON evidence: QF_UFNRA + XOLVER_REAL_DIV_PURIFY=1 = correct 9 (no
regression vs OFF), 14 instant-unknowns→engine (recoverable→recoverable-slow),
**0 UNSOUND** (benchmark_results/inv_QF_UFNRA_flagon). QF_ANIA + hasEuf =
0 UNSOUND, correct 0→0 (benchmark_results/inv_QF_ANIA_fixed).

---

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

### HARDENED 2026-05-29: all 73 QF_UFNIA instant-unknowns are NIA/structural
Earlier verdict rested on 3 Zohar traces; the 73 instant-unknowns actually span
5 families (44 Zohar-ic, 25 Zohar-alive, 2 TwoSquares, 1+1 CLEARSY). Traced the
4 NON-Zohar ones (the only place a hidden my-lane bail could lurk) — all 4 reach
the engine, none is an atomization/routing bail:
- 20190906-CLEARSY/0001/00304 (sat): Full-effort modelCheck → unknowns=1,
  "Theory: unknown (no reason)" = NIA engine can't decide consistency (engine
  incompleteness).
- 20190909-CLEARSY/0021/00001 (sat): "NIA: pending unknown (opposite polarity)"
  = NiaSolver.cpp:237 floor (same structural floor as Zohar).
- TwoSquares/z3.704037 + z3.704066 (BOTH oracle=unsat): Full-effort modelCheck
  returns consistent=1 on an UNSAT formula (NIA can't refute → spurious
  "consistent" model), then strict-validation floor → unknown ("model not
  positively confirmed (Indeterminate)"). The floor is CORRECT — promoting that
  model to SAT would be a FALSE-SAT (unsound). Real fix = NIA unsat-completeness,
  NOT my-lane model extraction. (Do NOT "recover" these — sound unknown is the
  right answer until NIA can prove unsat.)
VERDICT: zero hidden my-lane atomization/routing gaps in the QF_UFNIA flagship
instant-unknown set. The flagship conclusion (NIA-engine + structural) now holds
across all 5 families present, not just Zohar. EQ+NA my-lane is fully mapped +
closed; remaining throughput is NIA-engine/structural, handed off.

## ★ PRESOLVE-INFRA LANE (2026-05-29) — shared arith presolve (mine to fix)
Master redirect: own src/theory/arith/presolve/ (PresolveEngine,
IntLinearEqualityCoreHNF, IntegerLinearAlgebra) — the real EQ+NA wall, shared by
all arith theories. Findings via instrumentation:
- **SNF input matrix is ~87-98% EXACT-duplicate equality rows** (floppy2:
  19847 rows→415 unique; GrandProduct 593→77). SNF is super-linear in rows.
  SHIPPED row-dedup (a96d149, XOLVER_PRESOLVE_DEDUP_ROWS, default-OFF): skip
  byte-identical (coeffs,cst) rows (E∧E≡E, solution-set exact). reg 661/661
  OFF+ON, 0 unsound. floppy2 timeout(20s)→unknown(10.5s) (SNF wall gone;
  bottleneck moves to NIA opposite-polarity floor = structural).
- Exact-Amat CACHING (orig task) = only 18-58% recurrence (matrices grow per
  decision) → SUPERSEDED by dedup (~48x). Not pursued.
- **Presolve conflict was MAXIMALLY WEAK**: IntLinearEqualityCoreHNF existence
  conflict returned ALL equalities' literals (line 112) → blocks one assignment
  → no convergence. IMPLEMENTED IIS (XOLVER_PRESOLVE_IIS, default-OFF): SNF row
  i = combination U[i] of original eqs; conflict = only eqs with U[i][j]≠0
  (sound minimal infeasible subset). reg 661/661 OFF+ON. BUT: GrandProduct
  UNSAT is NONLINEAR (products) — HNF existence never fires there, so IIS
  doesn't help it. IIS targets the LINEAR-integer-infeasible class; measuring
  corpus benefit on QF_NIA sample (OFF=9/120 solved; ON pending).
- Re-profile lesson: dedup removed floppy2 SNF wall but bottleneck moved to the
  structural NIA opposite-polarity floor + NiaNormalizer::clearDenominators.
- **Post-dedup grandprod profile (5 samples): DIFFUSE** — no single dominant hot
  spot. Spread across LibPolyKernel::variables/getOrCreateVar, FlatMonomialMap::
  canonicalize, GeneralSimplex::resetActiveBounds, SharedEqualityManager::
  checkDisequalityConflict. = "per-check overhead × MANY checks (172+)". The
  many-checks is driven by weak NONLINEAR conflicts (the model rejections are
  nonlinear NIA, not HNF) → fewer checks needs nonlinear-conflict generalization
  = NIA lane. Per-check micro-opts (variables() cache etc.) = diffuse, modest,
  non-converting, grey-lane (NIA/NRA backend) + PolyId-stability soundness risk
  → NOT pursued (poor ROI/risk).
- **PRESOLVE-LANE VERDICT**: dedup is the clean sound win (shipped, eliminates
  pathological ~48x SNF cost). IIS sound+gated (0 sample conversion). Neither
  CONVERTS sampled cases — the EQ+NA wall is the NIA nonlinear engine +
  structural SAT blowup, consistent across ALL my owned layers (SAT/combination/
  presolve). My layers are now sound + efficient; the real bottleneck is mapped
  and handed to NIA. Tasks #12 (presolve fixpoint: dominant stage was HNF SNF,
  fixed by dedup; rest diffuse) / #13 (shared linear infra: diffuse, grey-lane)
  = diminishing returns, documented.

## ★ SAT/COMBINATION-EFFICIENCY LANE (2026-05-29) — bottleneck map (profiling)
New lane: SAT/CDCL(T)/combination efficiency. Profiled the EQ+NA timeout
families (gdb-SIGINT + breakpoint counts). VERDICT: the EQ+NA timeouts are
**NIA-arith-engine-bound, NOT SAT/combination-bound** — the SAT-side flags I own
(ZOLVER_SAT_MIN / SAT_LEMMA_MGMT / COMB_CAREGRAPH) do NOT help (all timeout 30s
on grandproduct). My value here = the precise profiling handoffs below.

### COMPLETE EQ+NA bottleneck map (verified hot functions):
| family | hot function | lane | call pattern |
|--------|-------------|------|-------------|
| QF_ANIA/AUFNIA (SVCOMP floppy2/s3srvr, GrandProduct) | `smithNormalForm` ← `IntLinearEqualityCoreHNF::run` ← `NiaSolver::stagePresolveFixpoint` | **NIA presolve** | grandproduct: 172 Full model-checks, 39 presolve(SNF) in 7s, ~170ms/SNF, NEVER converges (30s t/o) |
| QF_UFNRA (hoenicke) | `CdcacCore::solveLevel` recursion → `signAtRational` | **NRA CDCAC** | deep CAD lifting |
| QF_UFNIA/UFDTNIA (Certora) | `UnivariateIntegerReasoner::divisors` (trial-div √2^256) | **NIA** | per cb_propagate; fix=XOLVER_NIA_DIVISOR_CAP |
| QF_UFNIA (Zohar) | CaDiCaL deep search ~9800 levels → opposite-polarity floor | **structural** | SAT blowup from define-fun expansion |

### HANDOFF TO NIA — smithNormalForm (the QF_ANIA/AUFNIA medal bottleneck):
`IntLinearEqualityCoreHNF::run` (src/theory/arith/presolve/IntLinearEqualityCoreHNF.cpp:74)
recomputes `smithNormalForm(Amat)` FRESH every call — NO cache/memo. On
GrandProduct/SVCOMP it runs ~39× in 7s (~170ms each) and the search never
converges. TWO levers (NIA's lane, I locate / they fix):
1. **Cache/incrementalize SNF** keyed by the linear-equality-core fingerprint
   (if Amat is stable across checks, ~39× win → likely in-budget). Or a cheap
   feasibility pre-check (rank/gcd) before the full SNF.
2. **Minimal infeasible subset (IIS) conflict**: the presolve UNSAT conflict
   does not generalize → SAT re-proposes 172 models. Returning a minimal
   infeasible core would block 2^(n-k) models per conflict (convergence).
CONCLUSION: EQ+NA medal throughput is gated by NIA presolve SNF cost +
conflict-core minimality, not the SAT/combination layer. SAT-side lane has
limited EQ+NA leverage (verified).

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
