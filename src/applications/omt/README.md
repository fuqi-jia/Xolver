# Optimization modulo theories

`Optimize.h` exposes `Problem`, `Objective`, `Answer` and `Solver`. Assertions and
objective expressions are native nodes. Objective direction, arithmetic or BV
ordering, and lexicographic/Pareto/independent priorities are explicit. Result
values use `RealValue`, including exact algebraic values when supported by a
backend. Status separates an attained optimum, infeasibility, an unattained
infimum, unboundedness, invalid input and unknown.

The executable backend performs lexicographic Boolean/bit-vector optimization
by successive BDD restrictions, preserving all previously optimized objectives.
BV objectives require explicit signed or unsigned ordering. Arithmetic
objectives and other priorities return unknown; their contracts remain available
for additional backends. A model is returned for an attained optimum.
