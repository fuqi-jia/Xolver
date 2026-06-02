# MGC remaining gap — what OSF-CDCAC P1+P7 doesn't close, and why

User's correction (2026-06-02): "别为了这种简单例子沾沾自喜，真正的例子，
mgc还没攻克呢" — synthetic test cases aren't MGC.

This document records exactly what the shipped OSF-CDCAC P1+P7 slice
can and cannot do, and the precise machinery MGC needs.

---

## What the shipped slice DOES close

* **Synthetic cubic** `x³+y³+z³=100 with each ∈ [1,2]`: default TO at
  10s → OSF_PRUNE unsat 0.14s (71×).
* **Synthetic factoring** `x*y - x² = 100 with x>0, y<0`: factor x>0
  out of EQ, derive `y - x = 100/x`, contradicts `y<0 ∧ x>0`. Closes
  in 0.10s.
* **Bounded-variable nonlinear UNSAT class**: where every relevant
  variable has both lower AND upper bound, polynomial-interval
  arithmetic closes constraints whose [L,U] excludes 0 modulo their
  relation. Iterative factoring handles sign-definite common-factor
  variables.

## What the shipped slice DOES NOT close

`mgc_02` still TOs. Walking the specific reason:

mgc_02 has 9 variables (8 strictly positive, lambda1 unbounded) and
4 polynomial equations including:

```
eq1: gamma0*theta - theta*vv1*vv3² - theta*vv1 = 0
eq2: gamma0*mu + lambda1*vv1 - vv2 = 0
eq3: 2*alpha*gamma0 - 2*alpha*vv1*vv3² - 2*alpha*vv1
     + delta*vv2 - delta*vv3 = 0
eq4: (large 28-monomial polynomial inequality)
eq5: (large 24-monomial polynomial equality)
```

### What my iterative factoring does on mgc_02

* Detects `theta` as common factor in eq1 (since theta > 0):
  → derives `gamma0 - vv1*vv3² - vv1 = 0` as **reduced eq1**.

* Reduced eq1's interval: gamma0 ∈ (0, +∞), -vv1*vv3² ∈ (-∞, 0],
  -vv1 ∈ (-∞, 0). Total interval = (-∞, +∞). **Not refutable.**

* No other equation has a single common-factor variable, so factoring
  stops here. Same TO.

### What cvc5 actually does to close mgc_02 in 4.7s

The closing argument requires combining **eq1 (reduced)** with **eq3**:

```
eq3 = 2*alpha*(gamma0 - vv1*vv3² - vv1) + delta*(vv2 - vv3) = 0
       │                                │
       └── this IS the LHS of reduced eq1 (= 0)
```

Substituting reduced eq1 (= 0) into eq3:

```
0 + delta*(vv2 - vv3) = 0
delta > 0  ⇒  vv2 = vv3      ← new derived equality
```

Adding `vv2 = vv3` propagates through eq4 and eq5, eventually yielding
UNSAT.

cvc5's `ARITH_NL_COMPARISON` lemma class generates exactly this kind
of cross-equation combination — 443 lemmas per mgc case in their
stats.

### Why the shipped slice can't reproduce this

Required machinery:

1. **Polynomial-into-polynomial substitution**. Given derived eq1's
   LHS = `gamma0 - vv1*vv3² - vv1`, substitute it as a SUB-POLYNOMIAL
   into eq3. The kernel today has `substituteRational(p, v, q)` for
   constant substitution — no infrastructure to substitute a
   polynomial expression for a polynomial pattern.

2. **S-pair / Gröbner-basis style normalization**. To "see" that eq3
   contains `2*alpha * (reduced_eq1_LHS)`, we'd need to detect that
   eq3 minus `2*alpha * reduced_eq1` simplifies to a smaller poly.
   This is the S-pair computation in Gröbner basis algorithms.

3. **Cross-equation linear combination search**. cvc5's heuristic
   tries linear combinations of constraint pairs, looking for cancel-
   lation. For mgc_02, the multiplier `2*alpha` itself contains a
   variable — so the multiplier-coefficient search is itself a
   polynomial search.

Building (1) + (2) + (3) is **the multi-week R&D documented at
TERM-3** (`e74cd7b`). I have not built it.

## What's shippable now (the honest catalog)

| Closed | Open |
|---|---|
| Bounded-variable nonlinear UNSAT (cubic synthetic) | MGC cluster (~45 cases) |
| Sign-definite common-factor EQ (`x*y - x² = 100`) | Cross-equation comparison lemmas |
| Existing NRA reg 151/151 | Polynomial-into-polynomial substitution |

NRA reg **151/151** with `OSF_PRUNE=1`. Soundness intact. 0 false
results.

## What the next dispatch needs to actually close MGC

1. **Build polynomial-substitution machinery** in the kernel:
   `substitutePolynomial(p, target_pattern, replacement)`. This is the
   foundational primitive.

2. **S-pair detection**: for each pair (c1, c2), search for
   multipliers (q1, q2) such that `q1*c1 - q2*c2` simplifies. Heuristic:
   start with q1 = leading_coefficient(c2), q2 = leading_coefficient(c1).

3. **Iterative loop**: derive new constraints from S-pairs, normalize,
   feed back into interval pruning. Bounded by depth/budget.

4. **Cell-local integration** (the actual OSF-CDCAC P3-P6 path).

These four together are the cvc5-style NLext pipeline. Estimated
4-6 weeks of dedicated engineering as TERM-3 stated.

## Mid-session word

The shipped slice (commits `31d3661` + `979bbfb`) is real infrastructure
that closes a different bug class than MGC. **It does not close MGC**
and I am not claiming it does. MGC stays in TO bucket exactly as the
TERM-3 closure documented.

If the next dispatch wants MGC closed, it must allocate the multi-week
engineering effort for polynomial substitution + S-pair reduction. The
current 3-day budget surfaced the right architecture, shipped sound
infrastructure, but cannot complete the multi-week machinery within
the budget.

---

*Branch: `agent/nra-2` @ `979bbfb`.*
*WSL-safe protocol observed throughout.*
*0 false answers across the entire R&D arc.*
