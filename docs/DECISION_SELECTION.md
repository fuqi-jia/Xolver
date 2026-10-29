# Selecting Boolean and theory decisions

Register a borrowed `xolver::Propagator` with `Solver::setPropagator()` before
`checkSat()`. It must outlive the call. The default behavior is unchanged.

```cpp
struct ResearchPolicy : xolver::Propagator {
    xolver::DecisionSource decisionSource(
        const xolver::DecisionContext& context) override {
        // Inspect context.level and context.requests, or state maintained by
        // onAssignment(), onBacktrack(), and onTheoryCheck().
        (void)context;
        return xolver::DecisionSource::SatActivity;
    }
};

ResearchPolicy policy;
solver.setPropagator(&policy);
auto result = solver.checkSat();
solver.clearPropagator();
```

`SatActivity` delegates variable and phase selection to the SAT backend over its
Boolean abstraction, including theory atoms. `TheoryModel` uses the existing
model-directed linear-atom selection and falls back to SAT when no evaluable
candidate is found. It is the default; this interface does not install a new
search algorithm or establish a faster policy.

An explicit unassigned signed literal from `decide()` takes priority over
`decisionSource()`. An already assigned literal is ignored; zero declines the
explicit choice. The context describes the current SAT search and must not be
retained by reference. Assignments and heuristic model phases are not logical
entailments. Every selected branch remains subject to propagation, theory
conflict handling and complete-model validation, regardless of decision source.
LRA and LIA retain their respective backtracking policies.
