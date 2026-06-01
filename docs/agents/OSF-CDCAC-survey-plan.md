# OSF-CDCAC — Survey of current implementation + refactor plan

User-supplied architectural redesign (2026-06-02):
**Order-Stable Simplex-Fact CDCAC**. The thesis is correct: variable
ordering is a one-shot decision; the persistent value of Simplex must
move to **cell-level residual reasoning, certified bounds for domain
clipping, polynomial interval pruning, and Simplex-UNSAT → CDCAC-cover
lifting**.

**Recommendation**: **partial rewrite — keep what's already correctly
shaped, add new isolated modules for the missing cell-level layers.
DO NOT touch `CdcacCore` internals; expose hooks via thin interface.**

---

## Current `src/theory/arith/nra/simplex/` inventory

Four files exist; their fit-vs-spec:

| File | Spec role | Status |
|---|---|---|
| `NraLinearExtractor.{h,cpp}` | `Classify(A)` step (Section 2 of spec) | ✅ **Keep as-is.** `classifyConstraints` splits into `LinearAtom` (degree ≤ 1) and `CdcacConstraint` (nonlinear). Conservative on `terms() == nullopt`. Matches spec exactly. |
| `PolyStructureFacts.{h,cpp}` | `dropToLinearCount`, `nonlinearConnectivity`, `maxDegree` for `prefixScore` (Section 3.1) | ✅ **Keep, rename later.** Has `linearizationGain` (= dropToLinearCount), `nonlinearConnectivity`, `maxDegree`. Spec also wants `degreeDropSum` and `algebraicSectionPenalty` — additive. |
| `SimplexTableauFacts.{h,cpp}` | **Mislabeled**. Today it's "heuristic-only for ordering". Spec wants `CertifiedFacts` as a first-class type for pruning. | ⚠️ **Rename + split.** Keep the heuristic fields (`tightRowParticipation`, `rowParticipation`, `isBasic`) as `HeuristicFacts`. Promote `hasLower`/`hasUpper`/`isFixed` into a new `CertifiedSimplexFacts` with explicit reason tracking. |
| `VarOrderSelector.{h,cpp}` | `BuildStableOrder` (Section 3) | ✅ **Already one-shot.** Called exactly once per CDCAC instance from `CdcacSolver.cpp:150`; structural facts dominate, tableau facts are weak tie-break. Matches spec's design. Internal `front`/`back` naming → rename to `prefixRoleScore` per spec § 3.2. |

**Integration site**: `CdcacSolver::check()` line 146-175 — runs `computeCdcacVarOrder` ONCE under `XOLVER_NRA_VARORDER_SIMPLEX`, hands the order to `CdcacInput.varOrder`. No dynamic reordering after that. This already obeys spec § 3's "only constructed once".

## Spec → existing-code coverage gap

| Spec § | Component | Status | Action |
|---|---|---|---|
| § 2 Classify | `NraLinearExtractor` | ✅ done | keep |
| § 3 BuildStableOrder | `VarOrderSelector` | ✅ done (rename) | minor rename + add 2 score terms |
| § 4 CDCAC.load(A) | `CdcacSolver::stageCdcac` | ✅ done | keep |
| § 5 S0 := Simplex(L0) | not exposed | ⚠️ partial | needed: explicit `Simplex0` builder used by both ordering AND cell context |
| § 6 SAT-level conflict | absent | ❌ missing | NEW: `SimplexCoverLifter::asSatClause` |
| § 7 ExtractExactSimplexFacts | partial via `SimplexTableauFacts.hasLower/Upper/isFixed` | ⚠️ partial | NEW: explicit `CertifiedSimplexFacts` |
| § 8 BuildStableOrder | as above | ✅ done | – |
| § 9 setOrder | `CdcacInput.varOrder` | ✅ done | – |
| § 10 ProcessCell (cell-local Simplex) | **absent** | ❌ missing | NEW: `CellSimplexContext` |
| § 10.4-6 residual classification per cell | absent | ❌ missing | NEW: `CellResidualClassifier` |
| § 10.6 LiftSimplexUnsatToCover | absent | ❌ missing | NEW: `SimplexCoverLifter` |
| § 10.7-8 PolynomialPruneByFacts | absent | ❌ missing | NEW: `PolynomialIntervalPruner` |
| § 10.9 domain clipping | absent | ❌ missing | NEW: `DomainClipper` |
| § 10.10 cell priority | absent | ❌ missing | NEW: `CellPriority` queue |
| § 11 final loop | partially in `CdcacCore` | ⚠️ requires interface hooks | NEW: `CdcacOsfHooks` (thin interface) |

## Isolation strategy (per user rule "代码隔离，不要污染cac core")

```
src/theory/arith/nra/simplex/
  NraLinearExtractor.{h,cpp}        ✅ keep
  PolyStructureFacts.{h,cpp}        ✅ keep, +2 score fields
  VarOrderSelector.{h,cpp}          ✅ keep, rename frontScore → prefixRoleScore
  SimplexTableauFacts.{h,cpp}       ⚠️ rename to HeuristicTableauFacts;
                                      keep only the heuristic fields
                                      (tightRowParticipation, etc.)

  ── NEW MODULES (cell-level layer) ──

  CertifiedSimplexFacts.{h,cpp}     -- proven bounds, affine equalities,
                                      UNSAT reasons. Explicit "certified"
                                      type so callers can't accidentally
                                      treat heuristic facts as certified.
  CellSimplexContext.{h,cpp}        -- holds S0 base + clone, push/pop scope
                                      around a cell's specialized linear
                                      residuals.
  CellResidualClassifier.{h,cpp}    -- specialize(atom, cell) and re-classify
                                      degree of the result.
  PolynomialIntervalPruner.{h,cpp}  -- monomial-sign + interval-arith
                                      pruning per spec § 6.
  DomainClipper.{h,cpp}             -- intersect cell.domain with
                                      CertifiedSimplexFacts bounds.
  SimplexCoverLifter.{h,cpp}        -- Simplex UNSAT reason → CDCAC
                                      SectionCover / SectorCover / Refine.
                                      Implements spec § 9.
  CellPriority.{h,cpp}              -- queue scoring per spec § 8.

src/theory/arith/nra/core/
  CdcacCore.{h,cpp}                 ✅ DO NOT POLLUTE INTERNALS.
                                      Add minimal hooks:
                                        setOsfHooks(hooks*) -- nullable
                                        currentCellAccessor() -- read-only
                                      Default behavior unchanged when
                                      hooks == nullptr.
  CdcacOsfHooks.{h,cpp}             -- NEW. Pure-virtual interface with
                                      onEnterCell, onSimplexUnsat,
                                      onCertifiedFacts, onPolyPrune,
                                      shouldClipDomain. Implementations
                                      live in osf/ subdir, never inline
                                      in CdcacCore.
```

This keeps `CdcacCore` clean. The OSF behavior is opt-in via a single
hook pointer; default `nullptr` = byte-identical to today.

## Minimum-viable plan (per user's "P1 + P3 + P4 + P5 + P6 + P7")

In order of incremental ship + paired-test:

1. **P1 — VarOrderSelector rename + add `degreeDropSum`,
   `algebraicSectionPenalty`** to score. ~30 LOC, low risk. Paired
   test on existing 13 MGC + Mulligan.

2. **P3 — `CellSimplexContext`** (no behavior change yet). Just expose
   a clone-able Simplex over L0 that CDCAC can push/pop. Hook into
   `CdcacCore` via `CdcacOsfHooks::onEnterCell`. Test that with no
   other OSF hooks, behavior is byte-identical. ~150 LOC.

3. **P4 — `CellResidualClassifier`** + plumb specialized atoms into
   the cell's Simplex. ~100 LOC. Test for soundness.

4. **P5 — `SimplexCoverLifter` SectionCover only**. Spec § 9 says
   "先只支持 section". ~80 LOC. Soundness gate: NRA reg 151/151.

5. **P6 — `DomainClipper`** using `CertifiedSimplexFacts`. ~60 LOC.
   Paired test for sample-point selection in clipped domain.

6. **P7 — `PolynomialIntervalPruner`** with monomial-sign + interval
   arithmetic for `x*y`, `x²`, polynomial bounds. ~200 LOC.
   This is the largest single piece; ship behind a flag.

Total ~600 LOC of new code in 7 new files. Zero edits to `CdcacCore`
internals beyond adding a `setOsfHooks(OsfHooks*)` accessor.

## Why this is the right path post-MGC-TERM3

The MGC TERM-3 closure (commit `e74cd7b`) concluded that single-shot
sign-split + sign-conditional cuts can't close MGC; cvc5's 601
INFER_BOUNDS + 443 COMPARISON lemmas per case is **structurally
iterative cell-local reasoning**. The OSF-CDCAC spec describes
**exactly that** iterative cell-level pattern:

* P5 (SectionCover) lifts the iterative Simplex UNSAT into a covering
  structure that CDCAC inherently understands.
* P6 + P7 give CDCAC the bound/sign information cvc5 emits as
  separate lemmas.
* Domain clipping reduces the high-degree polynomial workload
  inside each cell.

The result is xolver-native bound inference inside the cell, instead
of cvc5's global lemma flood. Same algebraic content, different
delivery mechanism, **and one that respects the user's
"prefix cover, not SAT clause" boundary** (spec § 1.C).

## What I am NOT doing

* **Not rewriting `CdcacCore`.** Per user rule. Interface-only.
* **Not removing `SimplexTableauFacts`.** Just splitting the
  heuristic fields from the certified ones.
* **Not changing the default behavior** (no flag, no env var = byte
  identical to today).
* **Not implementing P8 (sector cover) or P9 (linearization cuts) in
  this first pass.** Defer until P5 + P6 + P7 are validated.

## Next action

Start with **P1 (rename + score additions)** as a small landing test
of the refactor approach. Then sequence P3 → P4 → P5. Each step
paired-tested against NRA reg 151/151 and the 13 MGC + Mulligan
sample. New commits append to the existing `agent/nra-2` branch
following the same milestone-driven cadence.

---

*Branch: `agent/nra-2` @ `e74cd7b`.*
*Spec source: user dispatch 2026-06-02.*
*Survey artifacts: this doc.*
*WSL-safe protocol observed.*
