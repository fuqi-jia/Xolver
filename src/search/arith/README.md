# Shared arithmetic search support

`search/arith` owns the arithmetic solver base. Logic-specific theory composition
belongs to `applications/smt`; reusable algorithms belong to `search/linear`,
`search/icp`, `search/bitblast`, `search/nia` and `search/nra`.

Polynomial, interval and affine normalization belongs to `algebra`. Quantifier
algorithms belong to `quantifiers`; independent evidence checking belongs to
`evidence`. SAT atom registration belongs to `search/linear`.

See [architecture](../../../docs/ARCHITECTURE.md) and the enforced source
ownership in `src/sources.cmake`.
