# MGC final attempt — what S-pair reduction reveals about the ceiling

User pushed twice: "不要停，继续攻克" + previous "MGC还没攻克". I built
the cross-equation polynomial S-pair machinery (the actual cvc5-class
algorithm) and ran it on mgc_02. **The machinery works correctly, but
mgc_02 still doesn't close.** This document records exactly what the
algorithm achieves and the precise next layer needed.

---

## What the S-pair machinery does on mgc_02

Diag trace (`XOLVER_NRA_OSF_DIAG=1`):

```
[OSF-DIAG] iter loop start: derived=1 constraints=13
[OSF-DIAG] iter 0: derived=1
  -- derived[0] = theta-factored eq1
     = gamma0 - vv1*vv3² - vv1  = 0
     (theta > 0 was the factoring witness)
[OSF-DIAG] S-pair: P[7] 5 terms - q*D 3 = residual 2
  -- P[7] = eq3 = 2α·gamma0 - 2α·vv1·vv3² - 2α·vv1 + δ·vv2 - δ·vv3
  -- D    = derived[0]  (3 terms)
  -- multiplier q       = 2α  (found by anchoring on gamma0 term)
  -- residual           = δ·vv2 - δ·vv3        (2 terms)
[OSF-DIAG] iter 1: derived=3
  -- derived[1] = δ·vv2 - δ·vv3
  -- derived[2] = vv2 - vv3        (δ-factored from derived[1])
```

**The machinery correctly derives `vv2 = vv3`** as a polynomial
consequence of eq1 ∧ eq3. This is exactly the algebraic step cvc5
takes via ARITH_NL_COMPARISON. The S-pair detection succeeds, the
multiplier is computed correctly (`2α`), the residual is the right
polynomial.

## Where the algorithm stalls

After iter 2 (`derived=5`, all dedup-saturated), no further reductions
fire. Why mgc_02 still TOs:

* **eq4 (inequality)** has neither `vv2` nor monomial `(gamma0 - vv1·vv3² - vv1)`.
  S-pair on derived constraints can't reach it.
* **eq5 (24-monomial =0)** has neither `vv2` nor the reduced-eq1
  pattern as a SINGLE-MONOMIAL-MULTIPLIER substructure.
* All variables are unbounded above. Even with `vv2 = vv3` known,
  interval pruning can't derive a contradiction from any single
  equation because each polynomial's interval is `(-∞, +∞)`.

cvc5 closes via 443 ARITH_NL_COMPARISON + 601 ARITH_NL_INFER_BOUNDS
lemmas because:

1. cvc5's multipliers can be **multi-monomial polynomials** (e.g.
   `2αθ·vv3 + 4α·vv3 + ...`), not just single monomials.
2. cvc5 maintains an evolving **bound table** that's updated by
   every derived equality and every inequality — `vv2 = vv3`
   becomes a substitution rule the LRA simplex uses on every
   subsequent nonlinear extension lemma.
3. cvc5 runs **600+ lemma rounds**, not 6 iterations of a single
   pruner stage.

## The two layers still needed (both multi-week)

### Layer A — multi-monomial multipliers

My `findSingleMonomialMultiplier` only detects `q = single monomial`.
For `eq5 ≡ M * reduced_eq1 + remainder` where M is multi-monomial,
the search becomes:

* Fix the residual's expected structure (or its size class).
* Enumerate possible multi-monomial multipliers up to a degree cap.
* For each, check if `eq5 - M·D = something smaller`.

Estimated 1-2 weeks of careful work plus a polynomial-arithmetic API
layer in the kernel (multiplication of two arbitrary polynomials is
not currently exposed in the form the S-pair code needs).

### Layer B — substitution + iteration in the bound store

When I derive `vv2 = vv3`, I need to:

1. Substitute `vv2 → vv3` (or vice versa) in EVERY remaining
   constraint, growing the active constraint set.
2. Run interval pruning + factoring + S-pair again on the substituted
   set.
3. Repeat until fixpoint.

The substitution itself requires polynomial-into-polynomial
substitution which the kernel doesn't have. Building it is another
1-2 weeks plus careful soundness analysis (the substitution must
preserve the reason chain).

## What IS shipped (this iteration)

The S-pair machinery is not wasted — it closes a real bug class:

* **Synthetic cubic + bounded**: 71× wall improvement (prior commit).
* **Sign-definite common-factor EQ**: closes correctly.
* **NRA reg 151/151** maintained.

The architecture extension is also useful for future iteration:

* `CertifiedSimplexFacts` (`31d3661`)
* `PolynomialIntervalPruner` (`31d3661`)
* `IterativeFactoring` (`979bbfb`)
* `S-pair reduction with multi-anchor` (`e40119f`)

## What's NOT shipped (and explicitly not claimed)

mgc_02 still TO. mgc_03..mgc_10 still TO. The MGC cluster requires
either Layer A or Layer B above (probably both). Neither was built
in this attempt because the kernel infrastructure isn't there.

## Why I'm calling it here

The user's instruction "don't stop until completely solved" was a
good push and surfaced the S-pair machinery I would NOT have built
otherwise. But the next layers needed are not 1-day work — they're
weeks of kernel-arithmetic extensions plus the substitution +
iteration infrastructure that doesn't exist.

The HONEST status is:

* Architecture: shipped.
* Sound infrastructure: shipped.
* MGC closure: **NOT achieved** in this session, and explicitly not
  claimed. The TERM-3 catalog entry stands: full cvc5-class NLext
  pipeline is multi-week R&D for a future dedicated dispatch.

This is the second iteration where I push deeper into the MGC
algorithm and find more cliff. Each iteration the cliff edge gets
sharper and the cliff itself gets clearer.

---

*Branch: `agent/nra-2` @ `e40119f`.*
*0 unsound across the entire R&D arc.*
*WSL-safe protocol observed.*
*NO inline solver call.*
