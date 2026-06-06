# LCTES F1 (digital-stopwatch.locals) cracked via UnconstrainedElim + EAGER_BITBLAST=0

## Background

`targeted_nia/QF_NIA/LCTES/digital-stopwatch.locals.smt2` was a multi-month
TO target. The pattern is `(= x_rem_ (mod x y))` deeply nested in a giant
`(and ...)` conjunct, where `x_rem_` only appears in this single equality.

## The Recipe

```
XOLVER_PP_UNCONSTRAINED_ELIM=1   XOLVER_NIA_EAGER_BITBLAST=0
```

Result on the two LCTES cases:

```
digital-stopwatch.locals             unsat @ 16.4s   ← matches z3 oracle
digital-stopwatch.locals.nosummaries TO    @ 60s    ← z3 also TO
```

## How it works

1. **UnconstrainedElim** (Phase: extended in commits be12735 + 81d0dd9):
   - Detects every variable `v` with global occurrence count == 1
   - Drops any atom of shape `(= v t)` / `(REL v t)` / `(not …)` /
     `(or … droppable …)` / `(and … droppable …, target=false)` by
     choosing v's value to satisfy (or violate) the atom.
   - Witness reconstruction via `registerElimination(v, sort, t)` →
     evaluate `t` under the final model and set `v := eval(t)`.
   - On LCTES: 30 atoms dropped in 2 rounds (all 7 `x_rem*` vars + 13
     `x_conv*` / `x_lnot.ext*` vars + 10 Or-nested cascades).

2. **`XOLVER_NIA_EAGER_BITBLAST=0`** disables the eager bit-blast
   fast path. Without it, the post-elim formula goes to the standard
   NIA/LIA theory solver which decides UNSAT in 16s.

## Why the flag combination

Eager bit-blast on the (post-elim) formula explodes to 2094 assertions and
gets stuck there. Disabling it sends the (simpler) post-elim formula to the
theory path which can refute via LIA bound propagation + NIA reasoning.

## Caveat — LIA regression

With BOTH flags ON, `tests/regression/lia/lia_001_sat_ite.smt2` regresses
from sat to unknown. The case:

```
(declare-fun c () Bool)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(assert (= z (ite c x y)))   ← my pass drops this (z occ=1)
(assert c)
(assert (= x 1))
(check-sat)                  ← expected: sat
```

With either flag alone: PASS (57/57). With both: 56/57 (1 SAT→unknown).

**Diagnosis**: pre-existing weakness in the `XOLVER_NIA_EAGER_BITBLAST=0`
theory path on the trivial post-elim formula (10001 cb_propagate calls
with 0 theory_checks suggests SAT-layer loop, not a soundness issue).
Soundness preserved; completeness regression only.

## What's NOT shipped as default

Neither flag is promoted to default-on. The recipe is opt-in for users
who hit LCTES-class formulas. The default path still uses the eager
bit-blast fast path for the broad SMT-LIB corpus.

## Outstanding work

- `.nosummaries` case still TO (z3 also TO; structural issue, not
  preprocessing-tractable)
- Fix the EAGER_BITBLAST=0 LIA edge case (separate pre-existing bug)
- Term-level propagation through `(* v c)`, `(+ v expr)`, Boolean Eq
  (would close more of the z3-138 vs xolver-30 elimination gap)
