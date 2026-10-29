# Weighted MaxSAT application

`Solver(DecisionOracle).solve(Problem)` accepts hard DIMACS clauses and soft
clauses with exact nonnegative rational weights. Indices start at one; zero and
`INT_MIN` are invalid. An empty hard clause is infeasible; an empty soft clause
always incurs its weight. Unreferenced variables need no allocation.

The frontend constructs native Boolean formulas and reuses the
[MaxSMT engine](../maxsmt/README.md). Limits cover oracle calls, search states,
formula work and cooperative cancellation. `Optimal` requires complete evidence
for the reported cost; `Unknown` may retain an incumbent without claiming it is
optimal. The injected oracle must satisfy the decision contract.

Run `build/bin/xolver-api-examples`; unit tests compare rational optima against
independent truth-table enumeration. This initial bounded truth-pattern search
is suitable for API integration, not a claim of competitive large MaxSAT performance.
