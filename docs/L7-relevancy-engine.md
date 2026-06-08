# L7 — Program-level relevancy engine

Status: **BUILT + sound + default-OFF (2026-06-08).** The engine exists and is
correct; it is **NOT the cs_* closer** — measurement re-diagnosed cs_* (see §0).

## 0. MEASURED OUTCOME (2026-06-08) — engine built; cs_* is theory-prop-bound, not relevancy-bound

The relevancy engine was implemented end-to-end and validated:
- `src/sat/RelevancyEngine.{h,cpp}` — z3-style boolean relevancy (And/Or/Implies/
  Ite/Iff/Not rules, backtrackable trail, iterative DAG propagation). 7 unit
  cases (`tests/unit/test_relevancy_engine.cpp`), TDD red→green.
- `Atomizer::buildRelevancyGraph` — extracts the boolean skeleton from `memo_`+IR.
- `CadicalTheoryPropagator` drives it (`notify_assignment`→onAssign,
  `notify_new_decision_level`→pushLevel, `notify_backtrack`→popToLevel) and steers
  `cb_decide`→pickRelevantUnassigned. Gate `XOLVER_RELEVANCY` (default-OFF).
- **Sound:** unit 1427/1427; combination/array regression 210/210 0-unsound BOTH
  OFF and ON; pure decision heuristic (cannot change a verdict).

**But it does not move cs_*, and the measurement says why it cannot:**

cs_lazy_false-unreach (z3: unsat, 0.03s) has **761 asserts but only 2 `ite`,
72 `or`, 4 `and`, 0 `=>`** — it is a *flat top-level conjunction* of arithmetic/
array atoms (`(= |#sizeof~INT| 4)` …). The relevancy graph is 1045 nodes and
**95% of them are relevant** (990/1045): every conjunct is asserted, so every
conjunct is relevant. **There is no dead boolean branch to prune.**

| config | decisions | theoryAtomDecisions | relevant/total | verdict |
|---|---|---|---|---|
| default, OFF | 58445 | 44842 (77%) | — | TO |
| default, ON  | 44909 | 34717 | 990/1045 (95%) | TO |
| eager-stack, ON | 7962 | **0** | 990/1045 | TO (≈5 ms/theory-op) |

So in default config the search is **77% theory-atom decisions** (the SAT core
*guessing* arithmetic-atom truth because the theory layer doesn't propagate it);
under the eager stack theory atoms drop to 0 but only ~8k decisions remain and it
*still* TOs on slow eager theory checks. Either way the wall is **theory
reasoning, not boolean search** — and boolean relevancy is powerless on a flat
conjunction.

**z3 closes cs_lazy in 5 decisions / 68 propagations / 3 conflicts.** Those 68 are
*theory* propagations — z3 derives the conflict by propagating implied
(dis)equalities/bounds, never searching. That is the real cs_* lever:

> **The cs_* closer is theory-implied-literal propagation** (a `theory →
> propagator` channel that pushes entailed atoms as forced literals so the SAT
> core stops guessing them), NOT a boolean relevancy engine. This is the same
> conclusion the (a)/(b)/FIX-c lane reached from the other side; the relevancy
> experiment confirms it from the boolean side: there is nothing boolean to prune.

Disposition: keep `RelevancyEngine` default-OFF (correct, sound, reusable — it is
the right tool for boolean-heavy instances with real `ite`/disjunction trees, just
not for these flat BMC conjunctions). The next cs_* effort must target theory
propagation completeness (L8, below), not §1–§4 of this doc.

## L8 (next) — theory-implied-literal propagation (the actual cs_* closer)

Build a sound `theory → CadicalTheoryPropagator` implied-literal channel: when a
theory solver (LIA/NIA/EUF/array) *entails* an atom under the current assignment,
emit it as a propagated literal with a valid reason clause, so the SAT core never
decides it. Foundations already on the branch: (a) EUF e-prop
(`XOLVER_EUF_PROP_COMB`), (b) N-O default-disequal phase, and the
`takeEntailmentPropagations` drain. Gap = arithmetic bound/equality entailment +
array read-value entailment as *forced literals* (not Full-effort SAT splits),
with reason-clause validity gated by the wrong-UNSAT firewall (task #24).
SOUNDNESS-CRITICAL (a wrong reason clause = wrong UNSAT) — every implied literal
needs a model-checkable reason.

### L8 MEASURED (2026-06-08) — the cs_* wall is reason-clause RECONSTRUCTION

The existing arith implied-literal channel was measured exhaustively on all three
cs_* with `XOLVER_NIA_LINEAR_PROP=1 XOLVER_EUF_PROP_COMB=1` (instrument:
`XOLVER_NIA_LINPROP_DIAG=1` → `[LINPROP-scan]` + `[LINPROP-drop]`):

| run | formPinned | conflict | emitted |
|---|---|---|---|
| cs_lazy, pure arith | **0** | no | 0 |
| cs_lazy, +eager array (NO_PROP+ROW2_DISEQ+ROW2_CONST) | 2 | no | **0** |
| cs_lamport / cs_peterson, +eager array | 30 | no | **0** |

1. **cs_* is array-contradiction-bound, not arith-bound.** Pure-arith linear-prop
   pins *nothing* (the simplex over the asserted linear atoms is feasible alone);
   cs_lazy has 1137 select / 1824 store, cs_lamport/peterson ~2840 / ~3935. The
   contradiction is derived through array read-over-write, exactly z3's 68
   *theory* propagations — not boolean search (L7) and not arith pins.
2. **Every array-enabled arith pin is dropped by the sound firewall.** With the
   eager array stack the simplex *does* find pinned forms (the injected Row2
   equalities pin `bridge_selStore − bridge_selAJ = 0`), but `[LINPROP-drop]`
   shows **`reasons=2 notLive=2`** for every one: both reason literals are off the
   SAT trail. The Row2 const merge is recorded in the e-graph with an *empty*
   literal (`ArrayReasoner.cpp` ~554, a genuine zero-literal theorem), but the
   interface-equality emitted downstream carries a 2-literal EUF *explanation
   path* whose literals were never SAT-propagated onto the trail. The firewall
   (`NiaLinearDecider.cpp` ~232) correctly refuses them — emitting a literal whose
   reason isn't currently true would risk a wrong UNSAT.

**Conclusion (cs_* closer, refined to the data-structure level):** the lever is
**reason-clause reconstruction**. `InterfaceEq::reason` is a single `SatLit`
(`NiaSolver.h` ~467) and cannot carry a multi-literal array/EUF explanation; the
e-prop path that builds the interface equality must reconstruct the *valid* clause
— the trail literals (or unconditional ⊥) that entail the Row2 conclusion — so the
implied equality lands on the trail with a model-checkable reason, after which the
downstream arith pin's reasons become trail-true and it emits. This is task #24,
soundness-critical (a wrong reconstructed clause = wrong UNSAT), and invasive
(touches `InterfaceEq`/`ActiveNiaConstraint` single-reason assumption + the EUF
explanation→clause path). Start with fresh full context — do NOT bolt it on.

### L9 SHARPENED (2026-06-09) — the dropped reason is an UNASSIGNED eqLit (fixpoint/staleness, not just multi-lit)

Per-reason instrument (`[LINPROP-drop]` now prints `var:T/F/U`): every dropped pin
cites a **single** read-value interface-equality atom used as both bounds, and it
is **`U` (unassigned on the SAT trail)** — e.g. `satVar=10546 reasons=2 [ 10881:U
10881:U ]`. So the interface equality is in NIA's merged simplex set (it pins the
form) but its SAT atom was **never forced onto the trail** — its own literal is the
reason, unassigned.

Drain counts (cs_lazy, `XOLVER_NO_DIAG`/`XOLVER_L4R_DIAG`, full eager + linprop):
NIA `deduced=914 arrayPair=82`, pre-pass `buffered=66`, `interface-eq merges=50`.
So the channel forces *some* read-value eqLits but not the **chain**: the dropped
eqLit's `(¬reasons ∨ eqLit)` clause never becomes unit because its EUF-explanation
reasons depend on *other* still-unforced eqLits in the read-over-write chain (the
propagation fixpoint never closes), or it is a stale post-backtrack residual whose
`IFACE_LIFECYCLE` level-remove missed it.

**Refined cs_* closer (task #24, soundness-critical, fresh context):** force the
read-value equality **chain in dependency order to fixpoint**, each link's reason
being its real currently-true e-graph explanation (`prop.reasons` from
`EufSolver::getDeducedSharedEqualities`, NOT the eqLit itself). For unconditional
Row2-const merges (distinct constant indices, empty e-graph literal) the clause is
unit `[eqLit]` and must force immediately — verify those aren't being given a
self-referential reason. Also audit the `IFACE_LIFECYCLE` backtrack for stale
interface equalities (reason atom unassigned after backtrack). A wrong/stale reason
here = wrong UNSAT; this is why the firewall (correctly) drops today.

Instrument left in place (gated, zero-cost OFF): `[LINPROP-drop]` under
`XOLVER_NIA_LINPROP_DIAG` reports `satVar reasons notLive` for each firewall drop
— the measurement hook the reconstruction work will iterate against.

### L9 FIX SHIPPED (2026-06-09) — firewall now sees interface-eq reasons (`XOLVER_NIA_IFACE_PROP`, `9d5de42`)

The `U` (unassigned) verdict was a **firewall false negative**, not a stale reason:
`IFACE_LIFECYCLE` keeps interface (dis)equalities OFF `state_.trail`, yet
`stageLinearProp` built its currently-true map ONLY from `state_.trail`. So an
interface-equality atom genuinely assigned-true by CaDiCaL (and held in
`interfaceEqualities_`) read as `U`, dropping every read-value form-pin.

Fix (`XOLVER_NIA_IFACE_PROP`, default-OFF): also seed the firewall's `asserted` map
with the interface (dis)equality reason literals — currently-true facts NIA holds
off-trail. SOUND: the entailment clause `(¬reasons ∨ impliedAtom)` is a global
theory tautology, so honoring these reasons cannot change a verdict.

Result on cs_lazy: `[LINPROP-drop]` 100% → **0**; **theoryAtomDecisions 28972 →
8312 (−71%)**. Gate: unit 1427/1427; FULL regression **753/753 0-unsound** with
`XOLVER_NIA_LINEAR_PROP=1 XOLVER_NIA_IFACE_PROP=1`.

**Still TOs — the cascade STALLS.** After the equality form-pins emit, the
steady-state scan shows `formPinned=0` with ~720 arith atoms still unassigned, and
the root LP stays **feasible** (`conflict=no`). The equality links are exhausted;
the chain does not advance because the next read-over-write links are
**disequality-gated** (`select(store(a,i,v),j)` needs `i≠j` to reduce to
`select(a,j)`). So the remaining lever is the **disequality side**: ensure the
Row2 `i≠j` propagations (and the value equalities they unlock) fire and land —
likely the same off-trail-firewall pattern on the `proveSharedDisjoint` /
`XOLVER_NIA_NO_DISEQ` path. That is the next link (L10).

### L10 MEASURED (2026-06-09) — eager-flood vs lazy-underfire; the residual wall is per-check PERF

Measuring the array funnel under the full stack revealed the diseq stall is really
an **array-completion dilemma**, plus a perf hotspot:

| config (+L9 IFACE_PROP) | selects | row2Eligible | theoryAtomDec | result |
|---|---|---|---|---|
| eager `AX_ROW2_CONST` | 2417 → **11789** | 1303→2323 | 8312 | TO (O(N²) drowns) |
| `AX_LAZY` only | **188** (bounded) | **0** (Row2 off) | 1461 | TO (no read-over-write) |
| `AX_LAZY`+`ROW2_CONST`+`ROW2_DISEQ` | **212** (bounded) | 9→31 | **1461** (−95%) | TO (perf) |

1. **Eager floods**: `completeStoreSelects` synthesizes ~10k cross-product reads;
   `getDeducedSharedEqualities` is O(N²) over the growing select set → drowns.
2. **Lazy bounds the select set** (212) and L9 drops decisions −95% (1461), and with
   `ROW2_CONST`/`ROW2_DISEQ` Row2 *does* fire on the bounded set (eligible 31).
   This is the best config yet — bounded, Row2 active, −95% decisions.
3. **But it is now per-check PERF-bound, not search-bound.** SIGPROF leaf hotspots
   under `cb_propagate`: `GeneralSimplex::proveFixedValueImpl` **477**,
   `PresolveEngine::run` **133** (every check), `proveSharedDisjoint` **152**
   (O(idx²)). At steady state (`formPinned=0`) `collectLinearProp` still calls
   `proveFixedFormValue` on **all ~720 unassigned arith atoms every check** — each
   a simplex pin-query returning "not pinned" → pure waste.

**L11 next levers — perf RULED OUT (measured); demand-driven Row2 is the SOLE closer:**
- **(perf) RULED OUT.** Implemented + measured a `stageLinearProp` throttle
  (`XOLVER_NIA_LINPROP_EVERY=K`, since reverted): at K=8, checks/s stayed **~7/s
  (≈140 ms/check) UNCHANGED**, cs_lazy still TO. So `stageLinearProp` was NOT the
  per-check bottleneck — the cost is **distributed** (`PresolveEngine` every check +
  `proveSharedDisjoint` O(idx²) ~1500 pairs/check + linprop), and no single throttle
  moves checks/s. More fundamentally the search **does not converge** (~25k decisions,
  no conflict) because Row2 under-fires — perf is not the wall. Throttle reverted
  (sound but unproven; only reduces propagation).
- **(completeness, soundness-sensitive) — THE closer.** Demand-driven Row2: the lazy
  path under-fires Row2 (eligible 31), so the read-over-write contradiction is never
  built → search never converges. Fire Row2 for the *relevant* reads on the conflict
  path (z3 ≈ 68 props) without the eager cross-product flood. The select set is now
  small (212), so selective instantiation is tractable. This is the genuine cs_*
  closer; it instantiates array axioms, so it is soundness-sensitive — start fresh.

Best repro config: `XOLVER_NIA_NO_PROP=1 NIA_NO_DISEQ=1 AX_ROW2_DISEQ=1
AX_ROW2_CONST=1 AX_LAZY=1 NIA_LINEAR_PROP=1 EUF_PROP_COMB=1 NIA_IFACE_PROP=1`.

---

(Below: the ORIGINAL relevancy plan, retained for reference. §1's "27k
program-structure decisions" was measured under the eager stack; the §0 table
supersedes it — those residual decisions are theory-atom guesses + eager-check
cost, not prunable boolean structure.)

## 1. Why this exists — the original (superseded) boundary

Target cluster: `targeted_eqnia/QF_ANIA/UltimateAutomizer/cs_{lazy,lamport,peterson}_*.smt2`
(Ultimate concurrency BMC traces). All **UNSAT**; z3/cvc5 ≈ 0.03 s; xolver **TO** (60 s+).

Everything *below* the SAT search has been built, validated, and **measured to saturation**
this session — the wall is now isolated to exactly one subsystem.

cs_lazy with the full propagation stack
(`XOLVER_NIA_NO_PROP + NIA_NO_DISEQ + AX_ROW2_DISEQ + AX_ROW2_CONST + EUF_PROP_COMB`,
plus default-on phase-disequal from `8eb22d3`):

| layer | baseline | after stack | status |
|---|---|---|---|
| interface atoms (shared-eq/diseq) decided by SAT | 13107 | **0** | ✅ saturated |
| read-value eqs forced into NIA | ~0/check | saturated (theoryAtomDecisions=0) | ✅ saturated |
| **program-structure decisions** | — | **~27000** | ❌ THE WALL |

z3 `-st` cs_lazy: **5 decisions / 68 propagations / 3 conflicts**, 0.03 s
(formula: 765 asserts, 1137 select, 1824 store, 408 declares).

**Conclusion:** the Nelson-Oppen interface layer and the array read-value layer are no longer
the bottleneck. The SAT core is searching ~27k assignments over the *program boolean skeleton*
(thread interleavings / control flow) that z3 never explores because of **relevancy** + chained
propagation to the assertion. This is the only thing between xolver and z3 on cs_*.

## 2. What z3 does (reference: `reference/z3/src/smt/`)

- `smt_relevancy.{h,cpp}` — **relevancy propagation**. An atom is "relevant" only when it is
  needed to justify the truth of the current boolean assignment of the goal. z3 does NOT assign
  a theory value to, or decide, atoms in un-taken branches of an `ite`/`or`. For a BMC trace,
  the reads/guards of a program step are irrelevant until that step's control predicate is
  relevant-and-true. This keeps the live atom set tiny (z3: 5 decisions).
- `smt_case_split_queue` — case-split ordering integrates relevancy (decide relevant atoms).
- `theory_array.cpp` `set_prop_upward` — selective, relevancy-driven array-axiom instantiation
  (already mirrored on our side by the eager/lazy completion; not the gap anymore).
- Chained propagation: array-value → guard truth → next-step predicate → … → assertion conflict,
  all via incremental theory propagation on each assignment (68 props total).

## 3. xolver's architecture gap

- CDCL(T) main loop = CaDiCaL + `CadicalTheoryPropagator` (IPASIR-UP external propagator).
  There is **no relevancy notion**: CaDiCaL decides every observed atom by VSIDS; theory checks
  are throttled (`cb_propagate`, `max(3, size/10)` growth) and monolithic (full rebuild).
- `cb_decide` currently returns 0 (let CaDiCaL pick) except the off-by-default `XOLVER_LRA_DECIDE`.
- So xolver explores the full program-interleaving space; z3 prunes it to ~5.

## 4. Implementation plan (phased; soundness notes per phase)

**Phase 0 — instrument relevancy demand (1 session).**
Add a file-based diagnostic that, for cs_lazy, classifies the 27k decision atoms: program-counter /
guard / interleaving / aux-Tseitin. Confirm how few are on the actual conflict path (expect ≈ z3's
5–68). Tool: extend `XOLVER_COMB_DIAG` / `XOLVER_SAT_PROF`. This sizes the prize and validates the
relevancy hypothesis before building the engine.

**Phase 1 — relevancy tracking (the core, multi-session).**
Port z3's relevancy: maintain a `relevant` set seeded by the goal; propagate relevancy through the
boolean structure (an `or` marks one true disjunct relevant; an `ite` marks the taken branch).
Hook into `notify_assignment` / `notify_new_decision_level` / `notify_backtrack`. Needs the
boolean DAG structure (Tseitin parents) available to the propagator — check what
`Atomizer`/`CadicalTheoryPropagator` already retains; may need to thread the gate structure through.
SOUNDNESS: relevancy only restricts *work/decisions*; never changes satisfiability. Pure heuristic.

**Phase 2 — relevancy-guided decisions (SOUND, low risk).**
In `cb_decide`, prefer relevant unassigned atoms; deprioritize irrelevant ones (or decline → let
CaDiCaL pick among relevant). Decisions are backtrackable ⇒ **zero wrong-UNSAT risk**. This alone
should collapse the 27k → a small number if Phase 1 relevancy is accurate.

**Phase 3 — relevancy-bounded theory work.**
Skip theory checks/axiom instantiation for irrelevant atoms (perf; also fixes the L5
proveSharedDisjoint perf sink: 453k calls/300 checks). SOUNDNESS: under-approx, completeness-only.

## 5. Soundness gate (non-negotiable, every step)
- unit `./tests/xolver_unit_tests` (currently 1420/1420).
- regression: `python3 tools/run_regression.py --root tests/regression --logic <all combination/array> --solver build/bin/xolver --timeout 15 -j 2` → **0 UNSOUND**, no verdict regression, OFF and ON.
- The `8eb22d3` baseline: combination/array 210/210 0-unsound. Hold it.

## 6. Reproduction + tooling
- `XOLVER_SAT_PROF=1` → `/tmp/xolver_satprof.txt` (decisions / theoryAtomDecisions / Full-checks).
- `XOLVER_COMB_DIAG=1` → `/tmp/xolver_combdiag.txt` (interface emission funnel; arrSplit/dedEq/L5).
- `XOLVER_SAT_SAMPLE=1` SIGPROF sampler (worker-thread; `addr2line -f -C -e build/bin/xolver`).
- ALL diagnostics MUST be file-based — worker-thread stderr is suppressed.
- WSL: `cmake --build . -j 2` only (never concurrent builds — clobbers libxolver_core.a).
  Wrap runs: `( ulimit -v 8000000; timeout N ... )`. `cmd|tail` masks exit → use `${PIPESTATUS[0]}`.

## 7. What is already DONE (do not rebuild)
- (a) EUF e-prop in combination (`XOLVER_EUF_PROP_COMB`, gated) — `8eb22d3`.
- (b) N-O default-disequal phase (`SatSolver::setDefaultPhase`, default-on array-comb) — `8eb22d3`.
- Eager array propagation levers: `XOLVER_NIA_NO_PROP`, `NIA_NO_DISEQ`, `AX_ROW2_DISEQ`,
  `AX_ROW2_CONST`, `AX_LAZY`, `AX_FIXPOINT` — all built, sound, gated. Together they saturate
  the interface + value layers (decisions 13107→0) but do NOT close cs_* (program search remains).
- These are the foundation; L7 sits on top of them.
