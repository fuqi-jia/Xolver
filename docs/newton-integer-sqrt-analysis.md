# Integer-sqrt Newton-Raphson invariant prover — design

Target: `sqrtStep1.smt2` / `sqrtStep1a.smt2` (corpus oracle-UNSAT).

## Formula shape

```
(>= x 1) (>= oldres 1)
(<= (* oldres oldres) x)                        # oldres² ≤ x
(<= x (* 4 (* oldres oldres)))                  # x ≤ 4*oldres²
(= newres (div (+ oldres (div x oldres)) 2))    # newres = (oldres + ⌊x/oldres⌋)/2 floor
(not (and (< x (* (+ newres 1) (+ newres 1)))   # x < (newres+1)²
          (or (<= (* newres newres) (+ x newres))     # newres² ≤ x + newres
              (<= (* newres newres) (div (* 15625 x) 10000)))))  # newres² ≤ ⌊1.5625*x⌋
```

## Negated assertion expansion

NOT(A AND (B OR C)) = NOT(A) OR (NOT(B) AND NOT(C)), where
- A: `x < (newres+1)²`
- B: `newres² ≤ x + newres`
- C: `newres² ≤ ⌊1.5625*x⌋`

So negation = **Branch 1**: `x ≥ (newres+1)²` OR
              **Branch 2**: `newres² > x + newres` AND `newres² > ⌊1.5625*x⌋`

For UNSAT, both branches must be infeasible.

## Branch 1 algebraic proof

**Setup with divmod witnesses**:
- Let q = ⌊x/oldres⌋, r = x - q*oldres, 0 ≤ r < oldres.
- Let p be the parity of (oldres + q), so newres = (oldres + q - p)/2, p ∈ {0, 1}.
- 2*newres = oldres + q - p.

**Derived bounds**:
- x ≥ oldres² and x = q*oldres + r imply q*oldres ≥ oldres² - r ≥ oldres² - oldres + 1, so q ≥ oldres - 1 + 1/oldres, hence q ≥ oldres for oldres ≥ 1.
- Similarly q ≤ ⌊x/oldres⌋ ≤ ⌊4*oldres²/oldres⌋ = 4*oldres.
- Therefore q ∈ [oldres, 4*oldres] and newres ∈ [oldres, (5*oldres - p)/2].

**Branch 1 contradiction**:
Branch 1 asserts x ≥ (newres+1)².
- x = q*oldres + r ≤ q*oldres + (oldres - 1) = (q+1)*oldres - 1.
- From 2*newres = oldres + q - p, q = 2*newres - oldres + p, so (q+1)*oldres - 1 = (2*newres - oldres + p + 1)*oldres - 1 = 2*newres*oldres - oldres² + (p+1)*oldres - 1.
- So x ≤ 2*newres*oldres - oldres² + 2*oldres - 1 (using p ≤ 1).

Combine with x ≥ (newres+1)² = newres² + 2*newres + 1:

  newres² + 2*newres + 1 ≤ 2*newres*oldres - oldres² + 2*oldres - 1
  ⇔ newres² + 2*newres + 1 - 2*newres*oldres + oldres² - 2*oldres + 1 ≤ 0
  ⇔ (newres - oldres)² + 2*(newres - oldres) + 2 ≤ 0
  ⇔ (newres - oldres + 1)² + 1 ≤ 0

This is **never true** for any integer newres, oldres. Therefore branch 1 is unsatisfiable. ∎

## Branch 2 algebraic proof (sketch)

Branch 2 asserts newres² > x + newres AND newres² > ⌊1.5625*x⌋.

Using x ≥ oldres² and newres = (oldres + q - p)/2 with q*oldres ≤ x ≤ (q+1)*oldres - 1:

  4*newres² = (oldres + q - p)²
  
For the first inequality (newres² > x + newres):
  4*newres² > 4*x + 4*newres
  (oldres + q - p)² > 4*x + 2*(oldres + q - p)
  (oldres - q)² + 4*oldres*q - 2p*(oldres + q) + p² > 4*x + 2*(oldres + q) - 2p
  
Using x = q*oldres + r:
  4*oldres*q ≤ 4*x (since r ≥ 0).
  
... continues with case analysis on p and r ...

The contradiction emerges because newres = ⌊(oldres + ⌊x/oldres⌋)/2⌋ is essentially the Newton step toward √x, and (oldres² ≤ x ≤ 4*oldres²) ensures newres² is within the 1.5625*x window.

## Implementation outline

1. **Template detector**: match `(= V (div (+ U (div X U)) 2))` where U, X, V are Int vars.
2. **Bound extractor**: find lower bounds `(<= (* U U) X)` and upper `(<= X (* C (* U U)))` for some constant C.
3. **Invariant generator**: emit:
   - `(>= V U)`  (newres ≥ oldres)
   - `(<= V (div (* 5 U) 2))` (newres ≤ 5*oldres/2)
   - The branch-1 contradiction lemma: `(or (< X (* (+ V 1) (+ V 1))) ...)` derived from completed-square identity.

4. **Algebraic validation**: each emitted lemma must pass exact polynomial identity check using libpoly's polynomial arithmetic.

5. **Hook**: new env-gated preprocess pass `XOLVER_PP_NEWTON_INT_SQRT` (default-OFF).

## Status

- Manual algebraic proof: complete for branch 1.
- Branch 2 needs case analysis; deferred.
- Implementation scaffolding: pending (multi-iter project).
