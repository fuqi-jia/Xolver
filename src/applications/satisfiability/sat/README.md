# SAT application

`Solver::solve(Problem)` accepts DIMACS clauses and assumptions (signed nonzero
indices), optional conflict/decision budgets and an absolute steady-clock deadline.
`variables=0` infers the range; sparse indices allocate only referenced variables.

The default factory creates the repository SAT backend. Inject a factory to use
another `SatSolver`. SAT assignments are checked against every original clause
and assumption. Invalid indices produce `InvalidInput`; exhausted or unsupported
budgets produce `Unknown`. UNSAT can include failed assumptions.

Run `build/bin/xolver-api-examples` for an executable example. The SMT frontend is
separate at `satisfiability/smt`; reusable CDCL infrastructure stays in `search/sat`.
