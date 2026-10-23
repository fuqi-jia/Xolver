# Verification conditions and inductive invariants

`Solver` checks each named obligation by asking an injected decision oracle
whether assumptions together with the negated conclusion are satisfiable.
Results distinguish validity, a counterexample, unknown and invalid input.

`InvariantSolver` accepts a transition system with current/next state pairs,
explicit immutable parameters, initial conditions, transitions, an invariant and
a safety property. It checks initiation, consecution and safety as three separate
obligations (indices 0, 1 and 2). Next-state substitution uses native node identity;
state predicates cannot contain undeclared or next-state free variables.

A result of Valid proves the supplied invariant is inductive and implies the
property under the supplied transition semantics. A failed induction obligation
is not necessarily a reachable program counterexample. Frontends supply integer
overflow, memory and transition semantics explicitly; no language semantics are
inferred by these interfaces.
