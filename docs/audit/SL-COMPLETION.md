# Quantified and inductive SL implementation progress

Status: implementation submitted for Panda1 validation; no server pass is claimed
in this document yet. Changes were developed in `build/parallel-sl-overlay` and
integrated by the root agent using before/after SHA-256 manifests. All C++
compilation and solver executions are reserved for ExperimentOS/Panda1.

The first build exposed doctest formatting errors; native0002 corrected those
and a recursive-symbol layout check. That build compiled, but three targeted
SL tests exhausted their unchanged budgets. The separate 55-case CLI audit had
39 conclusive answers, no wrong answers and 16 work-limit unknowns, all in
overlapping ownership or quantified two-cell star cases. Twenty models were
exported with no oracle rejection; four oracle queries and two model checks
were inconclusive. These failures are retained and are being addressed by
Boolean/constant simplification and fair retries, not by changing expectations.

Further server runs: native0003 passed 70/71 selected units (5,505/5,506
assertions), fixing countdown and quantified ownership but still exhausting the
two-cell list budget. Native0004 added calling-heap value freezing, explicit
unsupported-domain diagnostics and exact asserted-heap anchoring; it passed
72/74 units (5,584/5,586 assertions). The two-cell list SAT case now passes.
Execution then exposed the later overlapping-list UNSAT query and the new
spatial-ite integer-argument UNSAT case, both still work-limit Unknown. Earlier
REQUIRE failures had prevented later entries in those loops from running.
No full unit/CLI acceptance is claimed and expectations/budgets are unchanged.

The independent production model checker currently checks the transformed query
stored in the interpretation, not all original quantified/recursive assertions.
Original-input checks in selected tests and external cvc5 model pins cover only
those cases. Original SID/unfolding evidence remains a required separate step.

## Actual algorithms added

`NativeSpatialSearch` compiles a formula on a symbolic heap of exactly k cells
into PA. Each cell has an integer address and integer value, addresses are
pairwise distinct and differ from the separately interpreted nil. Points-to
requires exactly one cell; emp requires zero. Star enumerates all partitions of
these actual cells. Boolean connectives and Int/Bool quantifiers retain their
original scopes. Arithmetic ite conditions containing spatial formulas are
compiled on the same heap as their enclosing term.

When a wand antecedent has a proved cardinality bound B, its extension heaps are
encoded for every size from zero through B. Every extension address/value is
universally quantified, guarded by distinctness, non-nil and disjointness from
the current heap. The consequent is compiled on the union. Existential witnesses
inside the consequent remain inside these universal extension binders. They are
never replaced by one global witness.

Heap sizes increase from zero. A SAT PA assignment is combined with the exact
points-to heap and goes through the existing spatial and PA model checkers.
An exhausted finite cardinality search is not UNSAT. Global UNSAT from this path
requires a structurally proved bound on every satisfying heap: emp/pto bound
zero/one, conjunction takes an available minimum, disjunction requires both
bounds, star adds bounds, quantification preserves the body's bound, and
negation exchanges truth/falsity bounds. No QF small-model theorem is applied to
an arbitrary quantified or recursive query.

A second path uses polarity-aware finite quantifier instantiation. Integer
instances include nil and enumerate 0, 1, -1, 2, -2, ...; Bool is enumerated exactly.
Existential instances give lower approximations; universal instances give upper
approximations. Negation, implication antecedents and wand antecedents exchange
the approximation directions. Only a lower-approximation SAT model or an
upper-approximation UNSAT decision can settle the original query. This path
continues even when the fixed-heap path cannot establish a wand antecedent
cardinality bound. Positive forall witnesses are obtained by the separate exact
fixed-heap path, not by pretending finite instantiation establishes a universal.

A diagonal schedule introduces a new approximation depth each phase, retries
each unresolved older depth with a larger finite allowance, and caches settled
nonfinal polarities. The exact fixed-heap path receives a separate allowance.
An inconclusive old depth never prevents introduction of a newer one. Global work/depth/wall-clock exhaustion remains
Unknown. Some general formulas can keep refining forever without a bound or
inductive argument; that is an explicit incompleteness of this search.

## Recursive predicates

`NativeInductive` is an explicit least-fixed-point API. It validates every
definition, including unused ones, before search. Predicates return Bool; formal
parameters have unique identities and Int/Bool sorts. Applications retain an
immutable recursive symbol identity, must match arity/sorts, and refer to the
provided definition environment. Binder scope is checked. Each unfolding
alpha-renames bound variables before parameter substitution, preventing captures
between successive recursive calls.

The API additionally accepts heap-dependent Bool actual parameters and Int
actuals whose ite conditions contain spatial predicates. These extend the usual
heap-independent first-order actual terms in SL-COMP. Their specified meaning is
value passing at the calling heap. A review exposed a substitution bug: in
`p(b) = sep(b, pto(1,0))`, substituting `emp` directly for b re-evaluated it on a
subheap, so `p(emp)` could acquire a spurious model. The pending callvalue patch
freezes each heap-dependent actual with a fresh binder:
`exists v. (v = actual and unfoldedBody[param := v])`. The equality stays at the
calling heap; uses of v inside star and wand are then heap independent. Bool,
Int spatial-ite, negative-call and wand regressions cover both verdict directions.
This patch is not claimed validated until its Panda1 run completes.

Only definitions proved positive in the recursive predicates are accepted for
this LFP API. Boolean negation, implication antecedents and wand antecedents
reverse positivity. An unproved non-monotone occurrence is not silently assigned
a least fixed point. For example, `p = not p` is rejected even when no assertion
mentions p. For positive definitions, iteration from false/true bounds the least
fixed point. Search increases unfolding depth and solves both polarities, keeping
quantified/spatial subformulas intact for `NativeSpatialSearch`. Failure of a
finite lower unfolding never proves UNSAT; a model of an upper unfolding never
proves SAT.

The theory choice follows the SL-COMP definition: its inductive predicate atoms
use least-fixed-point semantics, and `define-fun-rec` is the input encoding.
This is documented in the [official competition paper, Section 3](https://letonchanh.github.io/files/slcomp19.pdf)
and the [competition specification and fragment list](https://github.com/sl-comp/sl-comp.github.io#specification-and-rules).
Ordinary SMT recursive-function equations under `ALL` must not silently acquire
this inductive semantics.

The current SOMTParser `Options::setLogic` whitelist does not accept the SL-COMP
SHID logic names. The native library API can be tested now. CLI LFP dispatch needs
a separate upstream parser PR, merge to its main branch, and submodule update,
plus the prepared runtime definition-environment bridge. No third-party source
has been modified for this work.

## Evidence that is and is not provided

Every published SAT interpretation contains an actual finite heap and the
existing independent concrete heap checker must accept the solved formula.
PA model evidence is checked separately from search. The tests also recompile
the original quantified formula on the exported concrete heap using
`nativeValue`, so this second check does not reuse the symbolic heap assignment.
The external driver pins the entire heap, nil and exported free symbols into the
original quantified input and invokes cvc5 with a short timeout.

These checks do not constitute an independently replayed quantified-SL or LFP
certificate. PA `ModelEvidence` checks the projected free-variable formula after
quantifier elimination. It does not certify each quantifier elimination step.
The PA trace/Isabelle route exists separately, but has not been replayed for these
new SL inputs. Finite unfolding soundness currently rests on the checked polarity,
monotonicity and substitution code and its mathematical argument. No standalone
checker binds an exported unfolding derivation to the original SID yet. The
source-to-PA compiler is also not formally verified. Neither complete LFP proof
coverage nor end-to-end C++ formal verification is claimed.

## Tests and remaining delivery work

The quantified unit tests cover arbitrary alternation, positive forall SAT,
shadowing, negative quantifiers, Bool domains, spatial ite addresses/data, wand
witness dependence, universal extension refutation, and non-invention of a heap
UNSAT bound. Inductive tests cover two-cell lists, recursive alpha-renaming,
overlapping ownership, negative predicate queries, countdown depth, nonpositive
unused definitions, and an unproductive cycle that must not become SAT from its
upper approximation.

`tools/fuzz/fuzz_quantified_separation.py` contains 55 original cases: seven fixed
semantic regressions and 48 deterministic integer variants. Each candidate and
oracle invocation has a four-second default timeout. Oracle Unknown, model
Unknown and timeouts are retained as incomplete checks; they do not become
successes.

Still open: server compilation/results; accepted CLI SHID syntax upstream;
ordinary recursive-equation solving; record/finite/uninterpreted heap domains;
independent quantifier-elimination and unfolding certificates; stronger cyclic
or inductive refutation rules; and exact treatment of quantified wand extensions
without an antecedent cardinality bound. This is a concrete expansion of the
solver algorithms, not a claim that the complete requested SL solver is finished.
