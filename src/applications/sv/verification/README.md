# Verification conditions

`Solver.h` defines a list of named obligations, each containing assumptions and
a conclusion. Clients inject `DecisionOracle` to select their logic backend.
`Answer` identifies an invalid or unresolved obligation and carries the
counterexample when available. All obligations must be established before the
result is `Valid`; a bounded or inconclusive check never produces validity.
