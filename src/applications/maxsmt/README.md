# Weighted MaxSMT API

`Problem` combines Boolean hard constraints and weighted soft formulas over the
shared native DAG. Weights are exact, nonnegative rationals; labels are optional
metadata, and returned violation indices refer to the input order. A soft
formula may contain any theory supported by the injected `DecisionOracle`.

```cpp
using namespace xolver::applications::maxsmt;
Solver optimizer(myDecisionOracle);
Problem problem;
problem.hard = {hardFormula};
problem.soft = {{preferredA, mpq_class(3, 2), "A"},
                {preferredB, mpq_class(1), "B"}};
auto answer = optimizer.solve(problem);
```

The first backend searches soft-formula truth patterns in increasing exact
penalty order. Every query asserts the complete selected truth pattern together
with all hard constraints. It works without model evaluation, assumption APIs or
optimization support in the decision backend. This is a bounded exponential
reference implementation for small instances, not a scalable MaxSAT algorithm.

`Answer` distinguishes `Optimal`, `Infeasible`, `Unknown` and `InvalidInput`.
An unresolved cheaper pattern prevents an optimality claim. `cost` on `Unknown`
is a feasible incumbent; `lowerBound` remains a proven bound. Models are passed
through when supplied by the oracle. No model is required for a valid decision
oracle to establish feasibility.

`Limits` bounds decision calls, generated states and formula-construction work;
zero numeric limits mean unlimited. Cancellation is cooperative via
`std::stop_token`, checked between decision calls. The decision callback owns
its per-query budget and must return `Unknown` for incomplete reasoning.

See [`app/api_examples.cpp`](../../../app/api_examples.cpp) for a complete native
SMT backend adapter and a runnable weighted example:

```sh
./build/bin/xolver-api-examples
./build/tests/xolver_unit_tests --test-case='maxsmt:*,parallel:*'
```
