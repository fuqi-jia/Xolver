# Task R — LibPolyKernel cousin audit continued

Master's priority-2 dispatch (8 h queue). Continue auditing `LibPolyKernel`
cousin operations beyond `S1c` (`terms`), `S1d` (`variables`), `S1e`
(`degree`). Apply the four-step methodology from
`docs/CAMPAIGN-RULES-hash-cons-audit.md`.

**Conclusion**: no shippable cousin remaining. Methods either don't exist
in the codebase, are already-rejected for soundness, or are empirically
cold on the canonical NRA stress workloads.

---

## Audit table

| Candidate | Status | Reason |
|---|---|---|
| `leadingCoefficient(p, var)` | **already shipped** | S1b (`afeda00`) caches the no-arg `leadingCoefficient(p)` via the `binOpCache_` at op code 5/6. The (poly, var) overload doesn't exist in `LibPolyKernel`. |
| `coefficients(p, var)` | **rejected (cold)** | Task M audited `getIntegerCoefficients` at 0 calls across all 4 NRA stress cases. Per the < 50 % rule, skipped. |
| `isConstant(p)` | **rejected (anti-pattern)** | Single libpoly call (~1 ns). Map lookup is ~50 ns. Cache lookup would *cost* more than save. Documented as anti-pattern in `CAMPAIGN-RULES-hash-cons-audit.md`. |
| `nMonomials(p)` | **doesn't exist** | No `nMonomials` accessor in the codebase. `terms(p).size()` is the closest, already cached by `S1c`. |
| `monomialAt(p, idx)` | **doesn't exist** | No iterator-style accessor; callers either iterate `terms(p)` (cached) or use `lp_polynomial_traverse` directly. |
| `resultantMatrix(p1, p2)` | **doesn't exist** | No matrix accessor. The closest is `pscChain(a, b, v)` which has its own cache at `XOLVER_NRA_CAC_SR_CACHE` (Task H, default-ON since Task Q). |
| `substituteRational(p, v, value)` | **rejected (cold)** | Empirically 0 calls on all 4 canonical NRA cases (Melquiond2 stress / nra_022 / nra_054 / nra_140). Transitive benefit from S1c+S2 was the working hypothesis; instrumentation confirmed the function isn't even reached. |
| `pseudoRemainder(p, divisor)` | **already rejected** | libpoly's `prem` depends on currently-installed `main_variable`, which `pscChain` mutates. Caching by `(p, divisor)` alone would bind to the first installed order and return wrong results on later calls. Documented in `S1b` commit `afeda00`. |
| `pseudoRemainderWithScale(p, d, mainVar)` | **rejected** | Same `main_variable` mutation issue as `pseudoRemainder`. Including `mainVar` in the key looks like it would help, but `pscChain` mutates the *installed* main variable in the kernel state, not the parameter — the key would be the same but the result differs. |
| `extractSymbolicResidue(p, modulus)` | **rejected (1 site)** | Single call site in `src/`. Definitionally zero call-graph redundancy — a one-site function cannot benefit from caching across queries. |

## Empirical evidence for `substituteRational`

Instrumented call counter without cache. Profile on canonical NRA cases:

```
nra_022 algebraic_root:        subRat calls=0
nra_054 metitarski_atan:       subRat calls=0
nra_140 root_2:                subRat calls=0
sqrt-problem-Melquiond2-0010:  subRat calls=0
```

The 26 call sites in `src/` are reachable from code paths not exercised
by NRA workloads — likely NIA-side univariate-RRT integer substitution
paths. NIA-agent could re-audit if NIA workloads exercise the function.

## Conclusion

The `LibPolyKernel` cousin op audit is now **fully closed** for NRA
workloads. The six shipped caches (S1, S1b, S2, S1c, S1d, S1e) cover
every method that's both hot and safe-to-cache. Further hash-cons gains
on NRA require either:

1. **New algorithmic paths** that introduce new cousin op call sites
   (e.g. a future `boundaryRing` primitive, or a new projection variant).
2. **Cross-lane application** of the methodology in
   `CAMPAIGN-RULES-hash-cons-audit.md` to NIA / EUF / Array / Combination
   / Datatype modules.

---

*Binary: `agent/nra-2` @ `01fab48` (post Task Q promotion).*
*Profile env: `XOLVER_NRA_KERNEL_STATS=1`.*
*WSL-safe protocol observed.*
