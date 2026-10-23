# Heap reasoning and entailment

`Solver` decides native heap formulas. `EntailmentSolver` checks whether the
conjunction of `context.assertions` entails `conclusion` on the same heap, by
deciding antecedents together with the negated conclusion. Free constants are
universally quantified by this refutation. Valid results carry a certificate;
invalid results carry a counterheap when the backend supplies one.

Recursive definitions require explicit `RecursiveSemantics::LeastFixedPoint`.
An SMT recursive equation alone does not select least-fixed-point semantics.
All definitions are checked for scope and positivity, including unused ones.
The search combines lower and upper unfolding approximations: satisfiability
of the lower approximation establishes a witness, and unsatisfiability of the
upper approximation establishes nonexistence. Unresolved unfolding continues
until the work budget is exhausted.

`Request::invariantCandidates` associates a predicate symbol with a Boolean
property using that definition's formal-parameter node identities. Properties
can contain arithmetic and nonrecursive spatial operators. For the monotone
definition operator `F`, `InductiveInvariantSolver` proves `F(C) => C` for the
conjunction of retained properties. This establishes `lfp(F) => C`; query
assertions are never assumed in these unconditional predicate proofs.

Candidates are removed when their induction condition is satisfiable or unknown.
Every removal triggers another pass because other candidates may depend on the
removed property. Only proved properties strengthen upper approximations.
`EntailmentSolver` additionally tries `false` for each predicate, allowing empty
recursive cycles to be proved empty. These candidates follow user candidates in
the inference result's index space. `complete` means the candidate-elimination
procedure finished; it does not assert completeness of recursive SL solving.

For example, a countdown heap predicate with a base at zero and a recursive
branch guarded by `n > 0` can prove `p(n) => n >= 0` without unfolding an arbitrary
heap length. A predicate defined solely by `p(n) = p(n)` has an empty least fixed
point; a definition `p(n) = emp or p(n)` does not.

`EntailmentCertificateSolver` proves every supplied invariant again, rebuilds
the recorded upper approximation and checks its unsatisfiability. Rejection
means the certificate fails; it is not a countermodel of the recursive formula.
Certificates are native formula objects, not portable formal proof terms.
The retained nonrecursive induction obligations can be checked by an independent
SL solver. This does not prove the correctness of their C++ construction.

These interfaces support further inference and proof-search algorithms without
changing the problem contract. The current engine uses candidate induction and
unfolding; it does not implement general cyclic proofs or complete recursive SL.
Unsupported semantic combinations and resource exhaustion remain explicit
`Unknown` results. See [executable examples](../../../../tests/unit/test_sv_entailment.cpp).

The mathematical rule is monotone least-fixed-point induction; a separation-logic
treatment appears in [Krebbers, van der Maas and Tassi, Inductive Predicates via
Least Fixpoints in Higher-Order Separation Logic](https://iris-project.org/pdfs/2025-itp-inductive.pdf).
This application uses first-order heap predicates, not the paper's Iris logic.
