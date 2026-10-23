# Differential equations

`Problem` expresses native Boolean relations over real coordinates, explicit
parameters and derivative applications (`Jet`). Each jet identifies an unknown
field, a multi-index derivative and its evaluation arguments. Empty arguments
mean the current coordinates; explicit arguments describe initial or boundary
conditions. Equations may have local assumptions. ODE and PDE share this problem
contract, with ODE requiring one independent coordinate.

`Solver` searches polynomial function candidates over coordinates and declared real parameters, up to a configurable total
degree and monomial budget. It substitutes their derivatives into every obligation,
universally quantifies coordinates and parameters, and solves for coefficients.
Each returned function passes another exact substitution check. `Solved` means
these functions satisfy the supplied equations, not uniqueness or completeness.
An unsuccessful bounded ansatz returns unknown, never a claim that the original
differential problem has no solution.

The interface accepts general native equations. Non-polynomial operators,
unsupported quantified theories and algebraic coefficient serialization can
require another backend. Parameters must be declared explicitly so they
cannot silently become existential fitting variables. Jet arguments depending
on unknown fields require a different substitution backend.
