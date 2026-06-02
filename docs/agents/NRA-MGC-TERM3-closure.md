# MGC-RD Terminal State — TERM-3 architectural confirmation

User's 3-day R&D budget with continuous iteration. Reached terminal
state TERM-3 (architectural depth confirmed; sign-split + HigherMixed
insufficient for the MGC cluster).

## Final paired test (13 MGC × 4 arms at 15s)

```
arm definitions:
  off                     = no NRA-specific env levers
  SIGN-SPLIT              = XOLVER_NRA_SIGN_SPLIT=1
  NLEXT-HIGHER            = XOLVER_NRA_NLEXT_HIGHER=1
  SIGN-SPLIT + NLEXT-HIGHER  = both

mgc_02..mgc_10  (9 cases tested before saturating budget)
  Every case TO/15s under every arm. 0 recovery, 0 regression.
```

NRA reg **151/151** with each flag combo. Unit **1090/1090**. 0 unsound.

## Why the levers don't fire on MGC

* **SIGN-SPLIT** correctly identifies lambda1 (mgc) or v3 (Mulligan)
  as sign-blocking and emits the 3-way `(or (> v 0) (= v 0) (< v 0))`
  lemma. In each branch, the variable's sign is fixed.
* But the remaining equations in MGC are **mixed-sign** (e.g.
  `gamma0*theta - theta*vv1*vv3² - theta*vv1 = 0` has one positive
  monomial and two negative). Even with every variable's sign
  fixed, sign-refute can't close because the polynomial isn't
  sign-definite.
* **NLEXT-HIGHER** (HigherMixed) scaffolds the abstraction so the
  linearizer no longer drops the equations as unsupported, but the
  sign-conditional cuts it emits also require all factor signs to be
  known. Same blocker as sign-refute.
* Even composed (`arm_both`), no MGC case closes within 15 s.

## What cvc5 actually does (gap reconfirmed)

`cvc5 --verbose --stats` on mgc_02:

```
ARITH_NL_COMPARISON:      443 lemmas
ARITH_NL_INFER_BOUNDS_NT: 601 lemmas
ARITH_NL_SIGN:             68 lemmas
ARITH_ROW_IMPL:          2600 lemmas
ARITH_SPLIT_DEQ:           42 lemmas
ARITH_CONF_SIMPLEX:       215 conflicts
totalTime = 4752 ms
```

The closing is **cumulative bound inference + comparison**: each lemma
tightens a bound on a nonlinear sub-term, which the next lemma uses to
tighten another, until simplex finds a linear conflict. 601+443+68
lemmas combine into a chain of partial bound tightenings that ONLY
together close the polynomial system.

Single-shot sign-split + sign-conditional cuts cannot reproduce this
because:

1. The bound chain is **iterative** — each lemma's RHS becomes
   another's LHS. A one-pass NRA stage emits and moves on.
2. The lemmas target **nonlinear sub-terms** (e.g. `vv3²`,
   `theta*vv1*vv3²`), requiring a registry of those aux terms
   maintained across propagation rounds.
3. Comparison lemmas (`a < b` or `a ≤ b` for nonlinear sub-terms `a, b`)
   need an ordering that respects the linear relaxation, which xolver
   doesn't expose at the NRA stage level today.

Implementing the cvc5 NL extension pipeline is the multi-week R&D the
3-day budget can't cover. Per the master spec for TERM-3, this is the
expected closure.

## Concrete shipped value of the 3-day R&D

| Commit | Value |
|---|---|
| `48b12ee` CAC_ALL_EFFORTS source-default-ON | **Mulligan-0004c TO→0.41s, meti-tarski/sqrt 18× wall (9 OK @18s → 10 OK @1s).** This is the actual sprint-actionable win. |
| `ede895e` HigherMixed scaffold | Removes silent unsupported-rejection of x^n / x*y*z monomials. Sound infrastructure for future NL ext work. |
| `3c3762b` SIGN_SPLIT impl | Sound 3-way case-split lemma (user-caught soundness bug fixed pre-test). Available for future composition. |

The CAC_ALL_EFFORTS source-flip was a real sprint win: Mulligan
cluster is now solvable, meti-tarski/sqrt is 18× faster. This came
out of the deep MGC investigation even though MGC itself stays in TO.

## TERM-3 word

**Terminal state TERM-3 reached: 9 consecutive MGC cases confirmed
architectural (no surgical surface). The CDCAC + NL-ext pipeline
needed to match cvc5 on MGC is multi-week R&D beyond the 3-day
budget. SIGN-SPLIT and HigherMixed stay default-OFF as available
infrastructure for future composition; CAC_ALL_EFFORTS source-flip
is the shipped sprint win.**

NRA reg 151/151. Unit 1090/1090. 0 unsound throughout.

## Catalog entry for post-SMT-COMP

* **MGC cluster (~250 cases) post-SMT-COMP target**: implement the
  cvc5-style NL extension pipeline (bound inference + comparison
  lemmas + iterative refinement). Estimated 4-6 week sprint.
* **xolver infrastructure already in place**: SignDefinitenessRefuter,
  NraLinearizationAdapter, IncrementalLinearizer's auxiliary-variable
  abstraction. The new pipeline would extend these with iterative
  refinement loops.
* **NL ext API design** should be drawn from cvc5's
  `theory/arith/nl/ext/` directory structure (algorithm, not code).

---

*Branch: `agent/nra-2` @ `3c3762b`.*
*Total commits this R&D dispatch: 16, all 0-unsound.*
*WSL-safe protocol observed throughout.*
*NO inline solver call.*
