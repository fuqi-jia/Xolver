# MGC-RD Day 1 — End-of-day report

User dispatched 3-day R&D for MGC bottleneck. End-of-day status with
revised Day 2-3 plan after deeper analysis.

## What shipped today

| Commit | Phase | Outcome |
|---|---|---|
| `48b12ee` | (pre-RD) | NRA-COLLINS-BUDGET: CAC_ALL_EFFORTS default-ON. **Mulligan-0004c: TO→0.41 s, meti-tarski/sqrt 9 OK @18s → 10 OK @1s (18×).** |
| `6ab763b` | MGC-PROFILE | Per-stage timing scaffold. Bottleneck localized: CDCAC itself stuck on high-degree projection. |
| `751208b` | Phase 1.3 | NL-ext lemma audit. Root cause: `NonlinearTermAbstraction::detectNonlinearTerm` only handles `{x*y, x²}`; rejects `x^n`, `x*y*z`, mixed. |
| `ede895e` | Phase 2A scaffold | Added `NonlinearKind::HigherMixed`; sign-lemma path in IncrementalLinearizer for higher-degree monomials. Gated `XOLVER_NRA_NLEXT_HIGHER` default-OFF. |

NRA reg 151/151 throughout. Unit 1090/1090. **0 unsound.**

## Refined diagnosis: MGC needs SIGN-SPLIT, not just HigherMixed

Phase 2A scaffold compiles + runs, but doesn't yet close mgc_02. The
deeper reason emerged from re-reading the constraints:

mgc_02 has 9 vars. 8 have positive lower-bound constraints
(`(< (- v) 0)` ⇒ `v > 0`). **lambda1 has NO sign bound — unbounded**.

Equation: `gamma0*mu + lambda1*vv1 - vv2 = 0`

Sign analysis of monomials:
* `gamma0*mu`: positive (both > 0)
* `lambda1*vv1`: **Unknown** (lambda1 unknown ⇒ whole term indeterminate)
* `-vv2`: negative

The existing `SignDefinitenessRefuter` is BLOCKED by lambda1's unknown
sign. **My Phase 2A HigherMixed sign lemma is blocked by the same
issue** — it emits cuts only when all factor signs are known.

The actual closing requires **case-split on lambda1's sign**: emit a
theory lemma `(or (> lambda1 0) (= lambda1 0) (< lambda1 0))`. In each
branch, sign-definiteness fires (lambda1 sign-known) and the equation
becomes a definite sign contradiction.

This is **NRA-SIGN-SPLIT** (task #124), the exact lever I proposed
in NDEEP-4. So Day 2-3 pivot: ship the sign-split lemma generator.

## Day 2-3 plan

### Day 2 — SIGN-SPLIT implementation

1. **Detect sign-blocking variables**: walk `SignDefinitenessRefuter`'s
   indeterminate path. When a single sign-Unknown variable blocks a
   refutable constraint, record it as a split candidate.

2. **Emit case-split lemma**: for each candidate variable v, emit
   `(or (> v 0) (= v 0) (< v 0))` as a theory lemma. Atoms registered
   via `linAdapter_->registerAtom` or `registry_->getOrCreatePolynomialAtom`.

3. **Wire into NraSolver pipeline**: new stage `stageNraSignSplit`
   after `stageSignRefute`, before `stageLinearizeProbe`. Gated by
   `XOLVER_NRA_SIGN_SPLIT` (default OFF).

4. **Soundness**: each branch in the lemma is a tautology over reals;
   the disjunction is always true so adding it doesn't change the
   feasible region. Each branch, when entered, enables a sound
   sign-refute conflict.

### Day 3 — Validation

1. **NRA reg 151/151**: paired test default OFF vs ON.
2. **MGC sample paired**: mgc_02 through mgc_10 + a sample of Mulligan
   + atan/sin/exp meti-tarski cases — quantify recovery.
3. **Soundness**: 0 unsound mandatory (any false-UNSAT → revert).
4. **Promote** to source-default-ON if N_recovery ≥ 5 and 0 unsound.

## Phase 2A status — partial value

The HigherMixed scaffolding is NOT wasted:

* It removes the silent "unsupported" return for higher-degree
  monomials. After Day 2 (sign-split) lands, when the SAT layer
  enters a sign-branch and the variable becomes sign-fixed, the
  HigherMixed sign-lemma path DOES fire — giving the linearizer
  meaningful cuts on the higher-degree side.
* So Day 1 (HigherMixed) + Day 2 (sign-split) compose: sign-split
  resolves the unknown signs, HigherMixed emits the cuts.

## Day 2 morning checkpoint plan

1. Read `SignDefinitenessRefuter.cpp` for the indeterminate detection
   path (already audited at NDEEP-4).
2. Build a `findSignSplitCandidate` helper.
3. Wire `stageNraSignSplit` into the reasoner pipeline.
4. Implement atom registration for new sign atoms.
5. Paired test on mgc_02 first.

## Day 1 status word

**On-track**. Root cause is precisely located in two layers:
1. `NonlinearTermAbstraction` rejects higher-degree (fixed Day 1 scaffold)
2. `SignDefinitenessRefuter` blocked on unknown vars (Day 2 target)

Both layers needed. CAC_ALL_EFFORTS source-flip from earlier today
(`48b12ee`) already shipped real wins: Mulligan + meti-tarski/sqrt.
MGC closure needs Day 2 sign-split.

---

*Branch: `agent/nra-2` @ `ede895e`.*
*WSL-safe protocol observed (timeouts, ulimit, single-process).*
*NO inline solver call.*
