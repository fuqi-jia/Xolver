# Verification applications

PA and SL own their mathematical semantics and models. `verification::Solver`
accepts named verification conditions with explicit assumptions and a Boolean
conclusion. An injected decision oracle checks each assumptions-and-negated-
conclusion query. Unsatisfiability establishes that obligation; satisfiability
returns an invalid obligation and an optional counterexample. Unknown is
preserved. Program language, overflow and heap semantics must be supplied by the
frontend and are not inferred by the checker.
