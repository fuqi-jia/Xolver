# NOTES-eqna — EQ+NA unknown→verdict campaign

## ★★★★ DT AUDIT (2026-05-29, corpus provisioned by master) — QF_DT SEVERELY UNSOUND
QF_DT/QF_UFDT corpora now in-tree (QF_DT 8700/3-fam, QF_UFDT 203/2-fam). Family-
split audit vs z3:
- **QF_DT: 54-case sample, correct=10, UNSOUND=11, other=33 (z3 t/o).** ALL 11 are
  FALSE-SATs (xolver=sat, z3=unsat) — 9 Barrett-jsat + 2 blocksworld-BMC.
- QF_UFDT: 33-case sample, correct=3, UNSOUND=0, 30 t/o (z3 also t/o). 0-unsound
  but low coverage (hard-for-everyone).
**BUG CLASS (single, characterized): TESTER ON A CONSTRUCTOR-APPLICATION TERM not
refuted.** `(_ is C) (D ...)` with C≠D is definitionally FALSE (e.g. is_cons(null),
is_node(leaf …), is_null(cons …)), but DtReasoner returns sat — the tester is not
constrained false → false-SAT. DtReasoner::checkConflict tester-consistency check
(DtReasoner.cpp:109-140) SHOULD fire (arg's class holds constructor D; tester
target C; C≠D → conflict) but doesn't. Likely causes (need instrumentation to pin,
like the #12 XOLVER_DIAG_AMV approach): (a) the tester term isn't merged with
true/false so `isTrue/isFalse` stay false (line 120 skip), or (b) the empty-reason
skip (line 136 `if (!reasons.empty())`) drops the conflict when the arg IS the
constructor term (explainEquality(u,m) empty) — the correct conflict is the UNIT
clause ¬(is_C(...)) with reason = the asserted tester literal. QF_UFDT entry-safe (0-unsound) but perf-limited.

**★★ #19 FIXED (master-greenlit, 2026-05-29): the root was a PARSER bug, not the
DtReasoner.** Pinned via instrumentation (testerTerms=0 even in regression): the
indexed tester `(_ is C)` resolves to a registered FuncDec "is-C" and parseOper
applied it via applyFun → generic UF apply, NEVER NT_DT_TESTER → opaque → DtReasoner
never saw it. THREE coordinated fixes:
1. SOMTParser `expr_parser.cpp` (submodule, commit 2dd6dae on iterative-rewriter,
   PUSHED): route registered DT funcs through getDtFunctionKind before applyFun →
   tag (_ is C)/applied ctors/selectors with their DT node kind.
2. `Atomizer::isFormulaPositionTerm` += Kind::Tester (commit 1bb0ee3): a Bool-sorted
   tester routes through BoolTermAsFormula → interned as "#dt.is.<C>" → DtReasoner
   registers it.
3. `DtReasoner` tester-consistency: opName(tt)="is-<ctor>" was compared against the
   bare ctor name → never matched → a TRUE tester on a determined class spuriously
   conflicted (false-UNSAT, exposed once testers registered: dt_tester_reconstruct).
   Strip the "is-" prefix → compare the real target constructor.
RESULT: QF_DT 54-sample UNSOUND **11→2** (correct 10→19); all 9 Barrett-jsat
tester-on-constructor false-SATs → correct unsat. Gates: full reg 661/661 (global
parser change clean), DT reg 12/12, unit 895/895, **0 new unsound**.
RESIDUAL (2 blocksworld BMC, still false-SAT — #20): separate/harder DT class at
BMC scale (656L, 54 testers, declare-datatype singular); not the tester-on-
constructor bug. PENDING: SOMTParser gitlink bump (-> 2dd6dae) in the real
NLColver checkout — the worktree's third_party/SOMTParser is a SYMLINK (type-change
T) so the gitlink can't be committed here without corruption → master bumps it.

## ★★★★ MAJOR SOUNDNESS FINDING (2026-05-29): 14 pre-existing combination false-SATs
The cross-division audit surfaced **14 false-SATs (xolver=sat, z3=unsat) in the
combination logics** — ALL pre-existing (NOT caused by the Ext-witness array fix:
verified default==fix-on==sat), ALL in my lane (EUF/array/combination), ALL
DIVISION-SINKERS, NONE in the regression suite (escaped the 661/661 gate). This is
the top soundness priority (user: "0-unsound paramount", "就算pre-existing也要解决").

| logic | false-SATs | cases | floorable by XOLVER_ARRAY_COMB_VALIDATE_SAT? |
|-------|-----------|-------|---------------------------------------------|
| QF_ALIA | 1 | cvc/read2 | YES → unknown (verified) |
| QF_AUFLIA | 9 | check/array_incompleteness1, cvc/{add5,add6,read6,read7,fb_var_12_11,fb_var_33_6,fb_var_5_12,fb_var_6_12} | YES → all 9 unknown (verified) |
| QF_UFLIA | 4 | mathsat/Wisa/{xs-05,xs-06,xs-09}, wisas/xs_9_19 | NO (no arrays; strict-validation → TIMEOUT, not a clean floor) |

**ROOT CAUSE (shared): combination SAT is not ModelValidator-backed (invariant 1
violation).** The Nelson-Oppen arrangement declares a model "consistent" at the
Full-effort check while a conflict found mid-search escaped (the read2/Wisa
conflict-stickiness class). The array floor (XOLVER_ARRAY_COMB_VALIDATE_SAT,
shipped b27d7b6) requires POSITIVE validation for QF_ALIA/ALRA/AUFLIA/AUFLRA →
floors the 10 array-combination false-SATs. The 4 QF_UFLIA Wisa cases are EUF
cross-equality soundness (the false-UNSAT direction was fixed earlier per
[[project_wisa_varconst]]; this is the false-SAT residual) — NOT cleanly floorable
(UF apps → validator Indeterminate; strict-validation recovery times out). They
need EUF/combination conflict-soundness work = #12.

**★★ #12 SOLVED (2026-05-29, master-greenlit):** the over-floor root is the
VALIDATOR'S CHANNEL CHOICE for EUF-class scalars. Instrumented ArithModelValidator
(XOLVER_DIAG_AMV, reverted): the floor runs TWO validations — pass 1
(arrayModelDefinitelyViolates, NO real channel) resolves i,j via the TOKEN channel
(@e6≠@e3 distinct) → both assertions TRUE → correctly not-violated; pass 2
(modelPositivelyValidates, WITH setRealAssignments) resolves i,j via the REAL
channel where numericAssignments collapsed them to 0,0 (unconstrained-scalar
backfill mints 0) → `(not (= i j))` FALSE → spurious Violated → over-floor.
FIX (committed, NO new flag — part of the ARRAY_COMB_VALIDATE_SAT capability):
in modelPositivelyValidates, a scalar whose model value is an opaque EUF token
(`@…`) is routed through the TOKEN channel ONLY — excluded from numAsg, the
0-defaulting, AND the (filtered) real channel — so the authoritative EUF identity
(distinct token = distinct class) is used, not the spurious numeric collapse.
RESULT: alia_005/alra_010 → sat (recovered); read2 + all 9 QF_AUFLIA false-SATs →
unknown (floored); full reg DEFAULT 661/661 (NIA untouched — no @tokens →
filteredReal==numericAssignments); array-comb reg flag-ON 33/33. Sound (only
sat→unknown). **ARRAY_COMB_VALIDATE_SAT STAYS GATED** (master: soundness-touching
flags stay flags; master collapses into default in one batch after the
differential, which needs the optimization flags OFF). The floor is now CLEAN
(recovers genuine sats + floors all false-SATs) → ready for that collapse.
SCOPE: the fix recovers the ARRAY+ARITH EUF-scalar class (the suite cases
alia_005/alra_010). UF-HEAVY QF_AUFLIA benchmark sats are NOT recovered (correct
stays 36/92, UNSOUND 0) — UF applications return Indeterminate in the validator
regardless of scalar channel; recovering those needs UF MODEL CONSTRUCTION
(function interps the validator can evaluate) = a further #12 sub-item, sound
either way (the unrecovered ones stay free unknowns).

**★ #12 ACTIONABLE DESIGN (diagnosed precisely 2026-05-29):** the over-floor root
is NOT missing array interps — it is UNCONSTRAINED-SCALAR DEFAULTING. Dumped
alia_005's model via (get-model): it is VALID + complete — `a=(store (const 0) 1 2)`,
v=3, j=1, i=4 (i≠j satisfied, read-fallthrough holds). The get-model CLI path
(Solver.cpp ~2042 `emit.resolve`) assigns unconstrained scalars DISTINCT FRESH
values (freshNum/numericOpaque). But the floor's `modelPositivelyValidates`
(Solver.cpp:245-253) validates the RAW theoryManager.getModel() and defaults
unconstrained declared scalars to **0** → i=j=0 → spuriously violates `(not (= i j))`
→ Violated → over-floored. FIX: route the floor's validation through the SAME
distinct-scalar model construction the get-model path uses (assign unconstrained
declared scalars distinct fresh values respecting asserted diseqs), OR add
array+scalar-distinct support to CandidateModelSearch. read2 stays floored (unsat
→ Violated under any completion). CAUTION: `modelPositivelyValidates` is SHARED
with the default-ON niaSatFloor — changing scalar defaulting from 0→distinct-fresh
could over-floor genuine NIA sats that validate at 0. Must SCOPE the change to the
array-combination floor context + gate on full reg 661/661. Sound (only
sat→unknown), but completeness-sensitive → dedicated #12 pass, full-reg-gated.
Recovers alia_005/alra_010 (enables QF_ALIA default-ON) + the pure-array+arith
subset of the 17 over-floored AUFLIA sats (UF-heavy ones stay Indeterminate →
need UF model construction too).
INSTRUMENTED (2026-05-29, diag reverted): alia_005's floor model has
`numericAssignments: i=0 j=0` (COLLAPSED) but `assignments: i=@e6 j=@e3` (DISTINCT
opaque EUF tokens) + `arrayInterps: a(deflt=@def2,n=1)` (interp PRESENT). So the
numeric channel collapsed the EUF-distinct scalars to 0==0. ATTEMPT 2 (reverted):
mapped distinct "@" tokens → distinct numbers, overriding numAsg — STILL did not
recover alia_005 (read2 + the 9 AUFLIA false-SATs stayed floored throughout). So
the validator evaluates EUF scalars via the OPAQUE-TOKEN channel (tokAsg), not
numAsg, and the residual failure is in ArithModelValidator's select/equality
evaluation over an opaque-token + array-interp model (deflt=@def2 comparison),
NOT in the model extraction alone. TWO attempts failed (empty-interp, token→num).
#12 NEXT STEP: instrument ArithModelValidator itself (per-assertion sub-verdict +
how select(a,@e3) and (= @e6 @e3) evaluate) — likely the opaque-token equality /
array-deflt-token handling returns Indeterminate where it should be definite.
This is validator-internal, soundness-sensitive (it gates the floor's recovery) →
dedicated instrumented pass on ArithModelValidator. Floor stays default-OFF until
then (genuine sats over-floored). Floor itself is robust (all false-SATs floored
across every attempt).

**MEASURED COST (QF_AUFLIA sample, floor ON vs OFF):** UNSOUND 9→0 (all false-SATs
floored) BUT correct 53→36 — the floor over-floors **17 of ~24 genuine sats** to
unknown (UF apps + incomplete array models → validator Indeterminate → not
positively confirmed). So the floor is a NECESSARY-FOR-ENTRY soundness gate (can't
enter a division with 9 false-SATs) but BLUNT: it trades ~71% of genuine sats for
soundness. The REAL fix is #12 (N-O valid model construction): complete the
combined model so genuine sats validate positively → the floor then catches ONLY
the false-SATs (recover the 17+2 lost sats). Floor = sound floor; #12 = recover.

**PROMOTION RECOMMENDATION (for master):** XOLVER_ARRAY_COMB_VALIDATE_SAT is
MANDATORY to enter QF_ALIA/QF_AUFLIA soundly (without it: 10 division-sinking
false-SATs). But default-ON today costs heavy completeness (QF_AUFLIA 53→36 solved,
2 suite sats alia_005/alra_010 → unknown). RECOMMENDATION: (a) the floor is the
soundness prerequisite for entering these divisions — enable it whenever entering
QF_ALIA/AUFLIA; (b) PRIORITIZE #12 combination model construction to recover the
over-floored genuine sats (turns sound-but-low-solve into sound-AND-complete);
(c) keep default-OFF until #12 lands (else suite 661→659 + ~18% AUFLIA solve loss).
The 4 QF_UFLIA Wisa false-SATs are a SEPARATE EUF-soundness blocker (#17) with NO
clean floor — QF_UFLIA CANNOT be entered until fixed at the EUF level.

## ★★★ ENTRY-READINESS EVIDENCE (task #14 — for the master's division-entry call)
Gate to enter a division: 0-unsound AND P(bug)<33%. My job = the evidence below.
All numbers are family-split samples vs z3 (NOT full corpus — directional).

| division | sample solved | 0-unsound? | gap class | entry posture |
|----------|---------------|-----------|-----------|---------------|
| QF_AX | 67/76 (88%) w/ array-fix ON | YES (MISMATCH 0) | array completeness mostly closed; residual = storecomm/swap (9) | STRONG: pure-array, fix shipped, 0-unsound across sample + 33 reg + 661 full reg. Promote XOLVER_AX_EXT_WITNESS_COMPLETE → enter. |
| QF_UF | 55/99 (56%) | YES (MISMATCH 0) | EUF perf — 44 transitivity-diamond TIMEOUTS (not unknowns) | SOUND but perf-limited. Entry safe (0-unsound); solve-count gated on e-propagation (diagnosed, deferred). Half-won. |
| QF_ALIA | 17/100 (17%) | NO — 1 false-SAT (read2) | array+LIA combination perf/completeness | BLOCKED on soundness: floor (XOLVER_ARRAY_COMB_VALIDATE_SAT) fixes read2 → then 0-unsound but low solve-rate (combination perf). Enter only floor-ON. |
| QF_AUFLIA | 53/92 (58%) | NO — 9 false-SATs (all floorable) | array+UF+LIA | BLOCKED on soundness: 9 false-SATs → floor-ON makes 0-unsound (cost: measuring genuine-sat loss). Highest combination solve-rate; promising once floored. |
| QF_UFLIA | 31/80 (39%) | NO — 4 Wisa false-SATs (NOT floorable) | UF+LIA combination | BLOCKED: 4 EUF Wisa false-SATs need EUF-soundness fix (#17), no clean floor. DO NOT ENTER until fixed. |
| QF_UFLRA | 34/61 (56%) | YES (MISMATCH 0) | UF+LRA combination, perf-limited | SOUND. Entry-safe (0-unsound); perf-limited solve-rate. The only CLEAN combination division. |
| QF_DT | 10/54 | NO — 11 false-SATs (tester-on-ctor) | DT theory soundness | BLOCKED: 11 tester-on-constructor false-SATs (#19), no DT model-validator backstop. DO NOT ENTER until fixed. |
| QF_UFDT | 3/33 | YES (MISMATCH 0) | DT+UF, mostly hard-for-everyone | SOUND but low coverage (30/33 timeout, z3 too). Entry-safe; few winnable. |

KEY: **the cross-division audit's headline = a SOUNDNESS problem, not a perf one.**
4 of 6 audited combination/array divisions have pre-existing false-SATs (QF_ALIA 1,
QF_AUFLIA 9, QF_UFLIA 4); only QF_UF, QF_AX, QF_UFLRA are 0-unsound as-is. The
array floor makes QF_ALIA+QF_AUFLIA sound (10 false-SATs → unknown). QF_UFLIA's 4
Wisa false-SATs are an EUF-soundness blocker (#17). STRONGEST entry candidates:
QF_AX (fix shipped, 88%, 0-unsound), QF_UFLRA (56%, 0-unsound clean), QF_UF (56%,
0-unsound). NONE of the false-SAT divisions may be entered until floored/fixed.

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
| QF_ALIA | 100 | 17 (17%) array-fix ON | 100 | **1** (read2, floorable) | recoverable-slow 45 (combination timeout), recoverable 20 | array+LIA combination perf/completeness + read2 false-SAT |
| QF_AUFLIA | 92 | 53 (58%) array-fix ON | 92 | **9** (all floorable) | recoverable 16, recoverable-slow 14 | array+UF+LIA: 9 pre-existing false-SATs (floored by XOLVER_ARRAY_COMB_VALIDATE_SAT) |
| QF_UFLIA | 80 | 31 (39%) | 80 | **4** (Wisa, NOT floorable) | recoverable-slow 33 (combination timeout), other 12 | UF+LIA: 4 Wisa false-SATs (EUF soundness #17), 33 combination-perf timeouts |
| QF_UFLRA | 61 | 34 (56%) | 61 | **0** | recoverable-slow 16, recoverable 2, other 9 | UF+LRA combination — CLEAN (0-unsound), perf-limited |

**QF_ALIA — SOUNDNESS BUG FOUND + FIXED (task #16):** audit surfaced
`QF_ALIA/cvc/read2.smt2` = **DEFAULT-PATH false-SAT** (xolver=sat, z3=unsat),
PRE-EXISTING (sat OFF and ON — my Ext-witness flag did NOT cause it), NOT in the
regression suite (escaped the 661/661 gate). It is the documented read2
conflict-stickiness residual (N-O arrangement declares consistent while a found
conflict escaped). Per user directive "就算pre-existing也要解决" + 0-unsound
paramount, FIXED via `arrayCombSatFloor` (Solver.cpp, flag
XOLVER_ARRAY_COMB_VALIDATE_SAT): QF_ALIA/ALRA/AUFLIA/AUFLRA SAT requires POSITIVE
ModelValidator confirmation (invariant 1) → read2's unconfirmable model
downgrades to unknown (VERIFIED: read2 sat→unknown under flag, sat with opt-out).
**DEFAULT-OFF + promotion gate (campaign policy: no default-ON until genuine-sat
losses recover).** Default-ON today regresses 2 GENUINE sats to unknown:
alia_005_sat_read_fallthrough + alra_010_sat_selfstore_nested_row2 (suite
661→659). Root cause of the over-floor: the combined model is INDETERMINATE to
the validator — declared array vars lack an interp AND/OR asserted-distinct
scalars (alia_005: i≠j) default to 0=0 → spurious violation; CandidateModelSearch
has NO array support so recovery fails. PROMOTION (default-ON + final-all-on)
GATED on #12 N-O valid model construction: assign asserted-distinct scalars
distinct values + emit interps for declared arrays so genuine sats validate
positively while read2 stays Violated→unknown. read2's correct-unsat recovery =
deeper N-O conflict-stickiness (structural, open). NET NOW: read2 false-SAT
eliminated under the flag (and in the final all-flags-ON build); default path
keeps the green suite; promotion path tracked. Engaged, not walked away.
**FAILED promotion attempt (don't retry):** hypothesized the over-floor was just
missing array interps → added empty default interps for declared arrays in
modelPositivelyValidates. alia_005/alra_010 STILL unknown flag-ON (read2 stayed
floored, good). So the gap is NOT merely the array interp — it is the deeper
combined-model construction (distinct asserted-diseq scalars in the typed
channel + array model with matching var-namespacing across getModel/IR/validator).
Reverted (ineffective). Default-ON promotion = genuine #12 work. Beyond read2, QF_ALIA
is far from won (17/100): 45 recoverable-slow = combination-perf timeouts, 20
instant recoverable = combination completeness gaps (next slices).

**QF_UF deep-dive (task #10, EUF perf):** 0-unsound, 55/99. ALL 44 losses are
TIMEOUTS (zero unknown) → PERFORMANCE, not incompleteness. Concentrated in the
synthetic equality-stress families eq_diamond/NEQ/PEQ/SEQ (Strichman-Rozanov
"minimum transitivity constraints for equality logic"). eq_diamond1 (trivial
`(not (= x0 x0))`) solves instantly; the sampled eq_diamond27..96 (95-302 lines)
are real transitivity chains → exponential without good conflict-learning /
transitivity-constraint generation. DEEPER + single-division + riskier than the
array lever. Documented; deferred behind the array fix.

**★ PROFILE (gdb SIGINT, 6 samples, eq_diamond27) — REFUTES cc/union-find
hypothesis.** Solve runs on a worker thread; ALL hot frames are in CaDiCaL, NONE
in congruence-closure/union-find:
- ~3/6 CaDiCaL inprocessing: `Closure::find_subsuming_clause` ←
  `forward_subsume_matching_clauses` ← `extract_gates` ← `inprobe` ←
  `cdcl_loop_with_inprocessing` (structural gate extraction / forward subsumption).
- ~2/6 conflict-analysis→backtrack: `analyze` → `backtrack` → `notify_backtrack`
  → `EufSolver::backtrackToLevel` (EUF only shows up as cheap backtrack bookkeeping).
- ~1/6 `external_propagate` → `add_external_clause` → `add_new_original_clause`.
ROOT CAUSE = lazy-SMT search explosion from MISSING EUF THEORY PROPAGATION: EUF
emits only conflict/blocking clauses (no entailed-(dis)equality propagation), so
CaDiCaL enumerates a huge tree → many conflicts → growing clause DB → expensive
inprocessing. RollbackUnionFind is union-by-size O(log n) — NOT the bottleneck.
Framework HAS the hook (`TheorySolver::takeEntailmentPropagations`, used by LRA
via XOLVER_LRA_PROP, kind=Entailment); EufSolver does NOT override it.
TWO LEVERS:
- QUICK (TESTED → FAILED, reverted): `configure("probe",0)`. Measured on
  eq_diamond27/35/41 + NEQ/PEQ: ALL still timeout OFF==ON. The search thrash
  (analyze/backtrack, ~1/3 of samples) dominates independent of inprocessing, so
  killing probing doesn't convert any diamond. Reverted (no value, keep tree clean).
- DEEP (right fix): EUF e-propagation — propagate entailed equality atoms
  (find(a)==find(b)) so the SAT solver never branches on chain equalities.
  SOUND-BY-CONSTRUCTION recipe: propagation is OPTIONAL, so verify-then-emit —
  before propagating, re-check via union-find over the explainEquality reason set
  that the reasons actually entail the merge (mirrors TheoryManager::
  conflictIsGenuine, TheoryManager.cpp:253); skip if unverified. A bad/incomplete
  proof-forest explanation → missed propagation, NEVER false-UNSAT. Atom pool is
  reachable via `registry_->records()`; combination mode already excluded
  (TheoryManager.cpp:206) → scopes cleanly to pure QF_UF.
  **WIRING BLOCKER (why deferred to a dedicated pass):** `takeEntailmentPropagations`
  is DEFINED (LraSolver+TheoryManager) but NEVER DRAINED — the propagator does not
  call it. And `cb_propagate` DROPS lemmas at Standard effort
  (CadicalTheoryPropagator.cpp:464 `(void)isLemma` — only CONFLICT clauses
  propagate during search; lemmas only flow from cb_check_found_model = full
  model, too late to prune). True implied-LITERAL propagation (return the entailed
  literal + lazy reason via CaDiCaL's cb_propagate-returns-lit + cb_add_reason_
  clause_lit protocol) is UNIMPLEMENTED. So this lever = a core CaDiCaL-external-
  propagator change, soundness-sensitive (division-sinking false-UNSAT risk if the
  reason clause is wrong) → dedicated focused pass, NOT a rushed tail-end edit
  (0-unsound is paramount). DIAGNOSIS COMPLETE; design + blocker handed off.

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
