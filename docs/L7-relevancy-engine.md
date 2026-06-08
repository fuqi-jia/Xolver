# L7 — Program-level relevancy engine (the cs_* closer)

Status: **open / fresh effort** (scoped 2026-06-08). Owner: TBD.
Branch base: `agent/nia-linear-prop @ 06141c9` (or a fresh branch off it).

## 1. Why this exists — the measured boundary

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
