# Optimization modulo theories

`Optimize.h` exposes general native assertions, objective expressions, directions,
ordering and priorities. Results separate attained optima, infeasibility,
unattained infima, unboundedness, invalid input and unknown. `RealValue` carries
exact objective values. An attained lexicographic optimum includes a joint model.

Boolean/bit-vector lexicographic optimization uses BDD restrictions. Arithmetic
lexicographic optimization compiles Boolean combinations of affine constraints
and uses rational simplex with integer branch and bound. It supports mixed
integer/real closed constraints and strict continuous real constraints. For an
open real optimum, a positive-slack feasibility query distinguishes an attained
optimum from an unattained bound. Disjunctions compare the complete lexicographic
results, including attainment at the first differing priority.

For unbounded results, `objectiveValues` contains the attained priority prefix;
the next objective is unbounded in its requested direction. For an unattained
infimum, the last value is the unattained bound and later priorities are absent.

BV objectives require explicit signedness. Pareto/independent priorities,
nonlinear arithmetic objectives, mixed BV/arithmetic optimization and open real
facets with integer variables need additional backends. These limitations do not
restrict the general problem contract. Resource exhaustion never certifies an
incumbent as optimal.
