# Heap reasoning and entailment

`Solver` decides native heap formulas. `EntailmentSolver` checks whether the
conjunction of `context.assertions` entails `conclusion` on the same heap, by
deciding antecedents together with the negated conclusion. Free constants are
universally quantified by this refutation. Valid results carry a certificate;
invalid results carry a counterheap when the backend supplies one.

For wand-free Boolean heap queries, model search first tries a heap built from a
positive spatial conjunct. The full formula and the independent heap evaluator
must both accept it. Failure continues the existing exhaustive heap search and
cannot establish unsatisfiability. This avoids enumerating arbitrary record
products before checking a heap already described by the antecedent.
Equality-only stack search enforces mandatory equalities, disequalities and
non-nil allocations while building each partition prefix. Branches of a
disjunction or wand do not supply mandatory constraints. In particular, distinct
integer literals no longer require enumerating all alias partitions first.

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
changing the problem contract. The engine combines invariant summaries,
simultaneous predicate induction, structural entailment rules and fair unfolding.
It does not implement complete recursive SL or arbitrary cyclic proofs.
Unsupported semantic combinations and resource exhaustion remain explicit
`Unknown` results. See [executable examples](../../../../tests/unit/test_sv_entailment.cpp).

The mathematical rule is monotone least-fixed-point induction; a separation-logic
treatment appears in [Krebbers, van der Maas and Tassi, Inductive Predicates via
Least Fixpoints in Higher-Order Separation Logic](https://iris-project.org/pdfs/2025-itp-inductive.pdf).
This application uses first-order heap predicates, not the paper's Iris logic.

`RelationSolver` accepts `RelationProblem` with predicate conclusions that may
themselves contain recursive calls. `EntailmentProblem::lemmaCandidates` supplies
such lemmas to `EntailmentSolver`; same-position relations between compatible
predicate signatures are also proposed automatically. Explicit candidates allow
different parameter maps, such as `p(x,y) => q(y,x)`.

Automatic proposals include conditional inclusions `p(args) => (guard =>
q(args))`. Guards come from heap-independent definition subformulas, their
negations and non-strict versions of strict arithmetic comparisons. These are
templates to prove, not assumptions. For example, a predicate that also accepts
negative inputs may include a zero-based countdown predicate only under `n >= 0`.
Closed lemmas can be used after contraposition when the original query is
negative; unproved induction hypotheses cannot be used there as global lemmas.
Unconditional relations are closed first. Conditional templates are explored
only for query-relevant directions that lack an unconditional inclusion. This
keeps unrelated guarded candidates from consuming the budget of a proof already
closed by ordinary mutual induction. All proposal and proof work shares the
entailment search budget.

The proof rule is simultaneous least-fixed-point induction. For the fixed
interpretation `P = lfp(F)`, retained conclusions form a vector `C(P)`. One exact
unfold of each antecedent definition precedes any use of an induction hypothesis;
its recursive calls are weakened using `C(P)`. The resulting body must imply the
conclusion, with right-hand calls unfolded exactly once. Hypotheses are never
applied to the unexpanded current antecedent or to generated conclusions. A
removed lemma weakens the hypotheses, so all survivors are checked again.
Query assertions do not justify global predicate lemmas. This is a simultaneous
fixed-point induction rule, including monotone definitions whose approximants
need not stabilize at finite unfolding depth.

Structural rules preserve Boolean implication, quantifier scope, and the
variance of negation and wand. Separating conjunction matches a bijection of
heap factors; it cannot discard an arbitrary heap frame. Heap-independent left
conjuncts provide pure assumptions that remain valid on subheaps. Nonrecursive
leaves are checked by the native SL backend. Recursive predicate symbols retain
their identities, and heap-dependent actual parameters are frozen on the calling
heap before substitution. Expansion, scope validation and capture avoidance are
shared by the inductive algorithms in `InductiveExpansion`.

Successful structural proofs return `EntailmentProof::StructuralInduction` with
all retained lemmas. Certificate replay proves every supplied lemma and closes
the original entailment again, without silently discarding an unproved lemma.
Failed proof attempts fall through to unfolding with the remaining shared work
budget. An open structural branch is not a counterexample. The nonrecursive
premises can be exported for independent checking; the structural proof-rule
implementation remains part of the trusted C++ code. See [relation and adversarial
examples](../../../../tests/unit/test_sv_relations.cpp).
