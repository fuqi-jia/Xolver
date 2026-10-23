# Constraint programming

`Problem` accepts native constraints, unrestricted/enumerated/interval domains,
all-different groups, allowed or forbidden tuple tables, element constraints and
Boolean cardinality bounds. Element indexing has an explicit base; an out-of-range
index makes the constraint false. Empty tables and empty cardinalities retain
their ordinary logical semantics.

`Solver` compiles these global constraints into native formulas and invokes an
injected `DecisionOracle`. The oracle controls the supported arithmetic and
other theories; application families do not include each other. A caller can
compose SMT with CP without changing the problem contract. Work limits constrain
formula construction, and unknown results retain the backend's reason.
