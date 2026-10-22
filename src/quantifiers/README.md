# Quantifier algorithms

This layer is above `search` and `algebra`, and below `logic` and `applications`.
It may use SAT, bit-blasting and arithmetic kernels; none of those lower layers
may include this layer. Thus a quantifier algorithm can use algebra without
creating an include cycle or moving the algorithm into algebra.

| Directory | Domain | Status |
| --- | --- | --- |
| `integer` | Integer/Boolean affine and divisibility formulas | Migrated existing elimination, native binder compilation, models and traces |
| `boolean` | QBF | Planned; no backend |
| `bitvector` | QBV | Planned; no backend |
| `real` | Quantified real arithmetic | Planned; no backend |

`integer/Elimination.h` consumes typed affine/divisibility formulas without
SOMTParser. `integer/NativeFormula.h` compiles native syntax, preserves binder
scopes and invokes projection within each scope. Numeric congruence, CRT and
witness calculations are lower-level mathematics in `algebra/integer`.
Both compilation and projection share the same resource accounting. A trace
is not automatically a proof of the complete input translation.
