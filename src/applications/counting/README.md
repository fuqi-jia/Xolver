# Projected model counting

`Problem` contains native assertions and an explicit tuple of distinct free
variables. Unprojected variables are existential; unused projected declarations
still contribute their domain. An empty tuple has zero or one satisfying value.
The result separates exact finite counts, infinite cardinality, invalid input
and unknown; finite counts use arbitrary-precision integers.

Bool/BV projection uses exact BDD counting. Linear integer/Boolean projection
uses exact mixed-integer bounds and tuple feasibility checks, with existential
integer or real variables. Overlapping disjuncts count each projected tuple once.
A feasible point and an improving rational recession ray certify infinitely
many discrete projected values. Bounded enumeration is resource-controlled.
Continuous projected variables, nonlinear counting and mixed BV/arithmetic
counting require additional backends. Unknown never carries a partial exact count.
