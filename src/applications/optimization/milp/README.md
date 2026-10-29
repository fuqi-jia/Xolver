# Mixed-integer linear optimization

`Problem` declares named continuous, integer or binary variables, optional
bounds, rational linear constraints, and a minimization or maximization
objective. Equalities and non-strict inequalities are supported. `Answer`
distinguishes optimal, infeasible, unbounded, invalid and unknown.

The backend uses exact two-phase rational simplex and integer branch and bound.
Variables may be unrestricted or have one-sided bounds; a finite box is not
required. Primal assignments and improving recession rays are checked against
the original constraints. An integer feasible point and a rational improving
ray establish mixed-integer unboundedness by scaling the ray to an integer step.

Work exhaustion returns unknown and may retain a feasible incumbent. Such an
incumbent is not an optimality certificate. The shared optimization algorithms
live in `search/optimization`; SMT and OMT use them without including MILP.
