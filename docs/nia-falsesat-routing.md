# NIA false-SAT (AProVE class) — diagnosis + routing (Agent 5 → Agent 2)

The ~357 QF_NIA AProVE false-SATs (oracle=unsat, default→sat) were tentatively
attributed to a frontend `BoolSubtermPurifier` `boolpur`-link bug. Investigation
of the concrete repro `benchmark/non-incremental/QF_NIA/AProVE/aproveSMT1072646210924280341.smt2`
shows that case is **NOT** a frontend bug — it is **NIA theory incompleteness**.

## Evidence (Agent 5)
- No `boolpur` / `ufbridge` vars are produced for this file (the negated
  conjunction's equalities sit in atomic-bool positions, so nothing is purified).
- Atom extraction is correct: `(= (* a4 a3) 0)` → `extractPolynomialConstraint`
  builds the nonlinear polynomial `a4·a3` and registers
  `PolynomialAtomPayload{diff=a4·a3, rel=Eq}`.
- NIA *can* refute a nonlinear disequality when the variable is pinned linearly:
  `(assert (= a2 0)) (assert (not (= (* a4 a2) 0)))` → zolver correctly UNSAT.
- Minimal false-SAT core (z3-oracle delta-debug, 10 conjuncts): a set of
  nonlinear `≥` inequalities + `(not (and (= (a4·a2−a4·a3) 0) (= a4·a2 0) (= a4·a3 0)))`
  whose only models force `a2=a3=0` *indirectly* through the nonlinear
  inequalities. z3=unsat; zolver returns sat with the **all-zero** candidate,
  which satisfies the inequalities but violates the negated conjunction
  (at all-zero the inner `and` is true → `not` is false).

## Root cause (Agent 2's lane: theory/arith/nia)
NIA returns "no conflict found" = sat with a candidate (all-zero) that satisfies
the nonlinear *inequalities* but violates an asserted nonlinear *disequality*,
without proving the system unsat and without validating the candidate against
all active constraints. The recovery (→ correct UNSAT) needs stronger nonlinear
unsat detection (the inequalities force a2=a3=0, which contradicts the
disequality) — NIA reasoning, not a frontend change.

## Floor in place (Agent 5)
`ZOLVER_PP_VALIDATE_NONLINEAR_SAT` (default OFF): when an incomplete nonlinear
theory is present (features.hasNonlinear), a Result::Sat is validated by
ArithModelValidator (invariant 1) and CMS-recovery; an unconfirmable model is
downgraded to `unknown`. Verified: aproveSMT1072… default=sat → floor=unknown;
genuine NIA sat (x∈{2,3}, x²≥4) stays sat. Narrower than the global
ZOLVER_PP_STRICT_VALIDATION (leaves complete logics untouched), so it is closer
to promotable for QF_NIA/NRA/NIRA once A2's recovery lands. Per the hard
promotion gate it stays OFF until the false-SATs are recovered to correct UNSAT
(promoting now would only inflate `unknown`).

## boolpur sub-class (Agent 2) — SCOPED, deferred to a fresh round

The 357 is **heterogeneous**. The case above (`aproveSMT1072…`) produces no
`boolpur` vars and is pure NIA incompleteness. A separate sub-class — AProVE
negated-conjunctions where the purifier *does* fire — has a distinct **frontend
ordering** root cause:

**Root cause:** `boolSortId_ == NullSort` for QF_NIA inputs with no Bool decls →
`Atomizer::isProvablyBool` (Atomizer.cpp:277) doesn't recognize the purifier's
fresh bool vars → the boolean `Distinct` is misrouted to NIA as a free integer
`Neq` (ArithAtomExtractor.cpp:103), decoupled from the arith equalities →
spurious SAT.

**DON'T repeat (both `bad_alloc`'d in the frontend):**
1. Not-as-iff `mkEq(fresh, ¬child)` → composite cascade.
2. Mint a sort via `allocateSortId` in the purifier ctor → collides with
   adapter-assigned Int/Real sort ids → type chaos.

**Safe path (next round):** `Solver.cpp:472-477` *already* has a safe
ensure-bool-sort (`allocateSortId` + `registerSort(Bool)` + `setBoolSortId`),
used by the atomizer at `:896`. The bug is **ordering** — `BoolSubtermPurifier`
runs at `Solver.cpp:651`, *before* `boolSortId_` is set. Fix = ensure the Bool
sort **before** `:651` (reuse that logic; reconcile with A1's `setBoolSortId` at
`:460`); do **not** mint in the purifier ctor. Caveat: confirm atomization of the
now-linked negated-conjunction doesn't itself blow up; then the harder half — NIA
must refute the linked arithmetic disequality → correct UNSAT.

Soundness meanwhile: A5's floor `a2e260a` (default-on) floors all 357 → `unknown`.
