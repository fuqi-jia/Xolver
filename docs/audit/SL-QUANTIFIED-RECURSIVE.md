# Quantified and recursive SL: delivery contract

The requested target is full language coverage with a working, sound, potentially
incomplete solver. An instance being difficult, or belonging to an undecidable
class, is not by itself a reason to stop immediately with `unknown`. Search must
continue under the configured resource limits. Missing implementation paths are
open delivery defects, not completed support for that class.

An exhausted time/work/memory budget must report its specific cause. A separate
semantic/algorithmic limitation must name the actual restriction and justify why
it blocks this input. No procedure can in general recognize every individually
unresolvable instance of an undecidable problem. An inconclusive bounded search
must not be reported as `unsat`, and a heuristic candidate must not be reported as
`sat` before its required evidence has been checked.

The parser representation is a SOMTParser assertion DAG plus its scoped recursive
definition environment. Recursive calls have immutable symbol identities;
function bodies are separate and acyclic. The parser does not assign least-fixed-
point semantics. SL's theory importer must distinguish inductive predicates from
ordinary recursive-function equations, preserve binding and polarity, and justify
the model/proof rules used for each accepted definition.

The next solver work includes spatial quantifiers, recursive unfolding with sound
lower/upper approximations, witness checking, and inductive refutation rules. A
lower approximation may establish satisfiability; its failure cannot refute the
original query. An upper approximation may establish unsatisfiability; its model
cannot certify the original query. Negation and wand antecedents reverse the
required approximation direction. Quantifiers under wand cannot be replaced by
globally fixed witnesses. A finite unfolding depth or heap cardinality becomes
an UNSAT bound only with an applicable bound theorem or checked inductive proof.
These obligations remain implementation work, not claims of completed algorithms.

Currently implemented: heap-independent quantified PA conditions can participate
in the native PA/SL combination, including alternation over Int/Bool. Direct
spatial quantification and recursive SL solving are still incomplete. Solver
certificates remain required; a formal refinement proof of the entire C++ program
is outside the user's requested SMT solver scope.

References for the semantic boundary and candidate decision procedures:
[Reynolds, Iosif and Serban: BSR separation logic](https://arxiv.org/abs/1610.04707)
and [Brotherston et al.: satisfiability with inductive predicates](https://discovery.ucl.ac.uk/id/eprint/1455002/).
Their decidable fragments must not be generalized to unrestricted integer-address
SL without establishing the additional assumptions.
