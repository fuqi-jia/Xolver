# Logical frameworks

`first_order` owns the generic backend contract and capability dispatch. It
accepts native formulas and application-supplied theory capabilities. It cannot
include application implementations, construct SV/PA or SV/SL, or fall back to
quantifier-free atomization. Concrete quantifier algorithms live one layer below,
in `quantifiers`, and can use `search` and `algebra`.

This migration provides the framework and the existing integer backend. It does
not implement general instantiation, MBQI, QBF, QBV or quantified real solving.
Unsupported capabilities remain explicit `unknown` results until those algorithms
are implemented. The mathematical integer backend still checks its exact grammar.
