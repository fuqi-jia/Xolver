# State verification

`Solver` checks each named obligation by asking an injected decision oracle
whether assumptions together with the negated conclusion are satisfiable.
Results distinguish validity, a counterexample, unknown and invalid input.

`TransitionSystem` declares current/next state pairs of identical sorts,
immutable parameters, per-transition nondeterministic inputs, initial conditions
`I`, transitions `T`, and a safety property `P`. Inputs receive fresh symbols at
each edge; parameters share one interpretation across the trace. State predicates
use current state and parameters only. Bound quantifier variables retain their
scope. Next-state substitution uses native node identity.

Implicit SL heap operators are rejected in transition formulas: a changing heap
must be represented explicitly as part of the state, for example with arrays.
Heap entailments use the separate SL application.

| Solver | Algorithm |
| --- | --- |
| `Solver` | Refute assumptions and the negated conclusion of each named condition |
| `InvariantSolver` | Check `I => C`, `C /\ T => C'`, and `C => P` (indices 0, 1, 2) |
| `InferenceSolver` | Houdini elimination of candidate conjuncts; recheck survivors whenever assumptions weaken |
| `SafetySolver` | Increasing-depth reachability, invariant strengthening, k-induction and simple-path completion |
| `CertificateSolver` | Rebuild and solve all conditions required by a supplied safety certificate |

`SafetySolver` checks `I(s0) /\ T(s0,u0,s1) /\ ... /\ !P(sk)` at increasing
depths. A satisfiable query gives the shortest discovered reachable counterexample,
with state/input frame symbols, the full path query and an optional backend model.
A certificate is returned only if an inductive invariant implies `P`, a k-step
induction condition holds after checking its base, or the absence of a simple
initial path proves that the checked depths cover every reachable state.

Supplied invariants are candidates, not trusted assumptions. Inference keeps
only candidates whose initiation and preservation queries are unsatisfiable.
Unknown candidates are discarded. Removing a conjunct weakens the induction
hypothesis, so remaining candidates are checked again. The empty conjunction is
`true`. Inference reports retained, refuted and undecided candidate indices.

`CheckLimits` bounds depth, formula construction work and oracle calls. A zero
work/query limit means unlimited; depth zero checks the initial state. The oracle
must enforce its own resource limits. Exhausting a budget, an inconclusive
reachable-path query, or an oracle exception returns `Unknown`. Absence of a
counterexample within a depth bound alone does not establish safety.

Certificates contain a proof method, depth and native invariant formulas.
`CertificateSolver` checks invariant initiation/preservation and the method's
base, induction or completion conditions against the supplied original system.
A rejected certificate does not necessarily indicate a reachable counterexample.
Replay is relative to the decision oracle; it is not a formal proof of the C++
implementation. Clients can inject a separate oracle for replay.

A result of Valid proves the supplied invariant is inductive and implies the
property under the supplied transition semantics. A failed induction obligation
is not necessarily a reachable program counterexample. Frontends supply integer
overflow, memory and transition semantics explicitly; no language semantics are
inferred by these interfaces.

[Executable examples](../../../../tests/unit/test_sv_model_checking.cpp) include
unbounded integer induction, two-step induction, fresh inputs, shortest traces,
forged certificates and finite BV graphs checked against independent BFS.

The induction rules follow the standard base/step formulation described in
[Gurfinkel and Ivrii, K-Induction without Unrolling](https://fmcad.org/FMCAD17/preprints/s6p3.pdf).
Candidate elimination follows the Houdini approach discussed in
[Lahiri and Vanegue, ExplainHoudini](https://www.microsoft.com/en-us/research/publication/explainhoudini-making-houdini-inference-transparent/).
