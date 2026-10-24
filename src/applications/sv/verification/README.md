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
| `ReachabilitySolver` | Exact existential successor images and symbolic reachable-region closure |
| `CertificateSolver` | Rebuild and solve all conditions required by a supplied safety certificate |
| `RangeSolver` | Prove sufficient mathematical-integer interval conditions from mandatory pure bounds |
| `RangeCertificateSolver` | Check each bound against its original assumption and replay the interval proof |
| `RangeAssistedSolver` | Check an interval certificate, otherwise solve the unchanged obligation with the injected oracle |

The range solvers accept the same native `Obligation` contract. The calculus and
certificate checker in `search/arith/IntegerBounds` also serve the standard SMT
application; SV adapts obligations to that shared interface. They use exact
integer interval operations, preserve symbol identity, and derive strict bounds
with integer rounding. They can bound nonlinear products and powers, select or
join conditional branches, and reason about Euclidean quotient/remainder ranges.
Zero can be excluded only by mandatory constraints, including explicit integer
disequalities; a condition inside a disjunction is insufficient. An open range
proof returns `Unknown`, never a fabricated countermodel. Countermodels in the
assisted solver come from its injected oracle.

Range certificates identify variable bounds and separate compound-term bounds,
with the exact original conjuncts that justify each endpoint. Replay checks membership, native identity,
endpoint values and the original conclusion without trusting the discovered box.
There is no implicit C arithmetic mode: source clients lower truncating or floor
division to ordinary native formulas before invoking these mathematical-integer
APIs. `intervalPow(interval, k)` and its rational counterpart denote the requested
`k`th power for every exponent; they do not switch meanings based on the client.
See the [QCP source bridge](../../../../tools/integration/README.md) for an external
client and its precise translation and validation boundaries.

`SafetySolver` checks `I(s0) /\ T(s0,u0,s1) /\ ... /\ !P(sk)` at increasing
depths. A satisfiable query gives the shortest discovered reachable counterexample,
with state/input frame symbols, the full path query and an optional backend model.
A certificate is returned only if an inductive invariant implies `P`, a k-step
induction condition holds after checking its base, or the absence of a simple
initial path proves that the checked depths cover every reachable state.

`ReachabilitySolver` accepts the same transition semantics without a candidate
invariant. It computes `E0 = I`, `E(k+1)(x) = exists s,u. Ek(s) /\ T(s,u,x)` and
`Rk = E0 or ... or Ek`. State and edge-input binders are fresh at every image;
parameters remain free and immutable. A satisfiable bounded path gives a concrete
counterexample. After all bases through `k` are checked, unsatisfiability of
`Rk /\ T /\ !Rk'` proves safety and produces `Rk` as an inductive-invariant
certificate for the existing `CertificateSolver`. No finite-state or rectangular
region assumption is used. Images can contain quantifiers; the oracle determines
which theory combinations it can decide. A closure query returning unknown does
not stop the bounded search; depth/work/query exhaustion remains explicit.

[Symbolic reachability examples](../../../../tests/unit/test_sv_reachability.cpp)
include an infinite reachable region with arbitrarily long spurious k-induction
paths, quantified inputs, immutable parameters, and finite graphs checked by BFS.

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
The image/fixed-point construction is described in [MIT's Symbolic Model Checking
lecture](https://ocw.mit.edu/courses/6-820-fundamentals-of-program-analysis-fall-2015/9d27e0c54dbbd68526a2d050e8f788d6_MIT6_820F15_L24.pdf).
