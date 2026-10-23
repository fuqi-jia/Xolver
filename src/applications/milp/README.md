# Mixed-integer linear optimization

`Problem` declares named continuous, integer or binary variables, optional
bounds, rational linear constraints, and a minimization or maximization
objective. Equalities and non-strict inequalities are supported by the contract.
`Answer` distinguishes optimal, infeasible, unbounded, invalid and unknown.

The backend infers simple bounds, enumerates bounded integer assignments and
checks continuous vertices using exact rational Gaussian elimination. A closed,
bounded nonempty feasible polytope has a vertex, so exhaustion of this search
establishes the reported optimum or infeasibility. Unbounded variable domains
require an additional backend and return unknown. Exhausted searches may retain
a feasible incumbent, but its value is not an optimality certificate.
