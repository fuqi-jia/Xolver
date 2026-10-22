# Boolean separation logic and independent heap semantics

The `sl::Formula` interface extends the earlier single-symbolic-heap API with
classical negation, conjunction and disjunction, separating conjunction, and
magic wand at arbitrary nesting. It also has location equality/disequality,
Boolean constants, `emp`, and exact singleton points-to atoms. The theory IR
contains only SL operators and heap records; it does not restore a general
CoreIR or copy SOMTParser terms.

Locations range over an infinite uninterpreted domain. Symbol 0 is nil and may
not be allocated. One heap signature fixes each record field as Location or
Integer. Location fields name interpreted symbols; integer fields are exact
decimal literals. The empty signature is allowed and has exactly one record
value. A formula DAG must be topologically ordered and type correct.

This is not yet the whole requested SL implementation. The native SMT-LIB/parser
integration described below passes the R22 server suites. Arithmetic expressions
in addresses/data and their PA combination, quantified
SL, recursive predicates/SIDs and their proof rules remain to be implemented.
The general quantified/inductive problem must not be claimed decidable merely
because this quantifier-free core has a complete finite abstraction.

## Finite abstraction

The small-model measure follows Section 4 of Reynolds, Iosif, Serban and King,
[A Decision Procedure for Separation Logic in SMT](https://arxiv.org/html/1603.06844):
emp and points-to have width 1; pure atoms have width 0; negation preserves
width; Boolean combinations take the maximum; star adds widths; wand takes
the consequent's width. The following describes this implementation's
specialization to the fixed record signature, not the paper's SMT reduction.

Fix a location interpretation. Retain separately every non-nil location value
mentioned in the formula. A named cell is either absent or contains a record
equal to one of the instantiated points-to records, or a record unequal to
all of them. The latter class needs one representative, except when the record
domain has only one value. At all unmentioned addresses only the number of
allocated cells is observable. Their addresses and fields cannot be inspected
by any atom.

For each subformula F, its truth as a function of that anonymous-cell count is
constant from width(F) onward, for every fixed configuration of named cells.
The structural argument is:

* Atomic spatial formulas distinguish zero, one and excess cells; pure atoms
  do not inspect the heap. Boolean operations preserve the stated thresholds.
* A star distributes the named cells and splits the anonymous count between
  its operands. Above the sum of the two thresholds, any excess can be placed
  in an already saturated operand. Conversely a saturated split can absorb
  any further anonymous cells. This gives the sum threshold.
* A wand ranges over disjoint extensions. Each extension fixes an antecedent
  truth value independently of the original anonymous count. Once that
  original count reaches the consequent threshold, the union is saturated
  for every extension. Hence the wand threshold is its consequent threshold.

For wand evaluation, it suffices to enumerate each possible configuration of
currently absent named cells and extension counts from zero through the
maximum of the antecedent and consequent thresholds. Larger extensions agree
with that final count in both operands. Fresh concrete addresses must avoid
the entire current heap, including its unmentioned cells.

Search enumerates location equality partitions with nil fixed, named-cell
record classes, and anonymous counts through the root threshold. This is a
complete representative enumeration for this signature, rather than a
user-selected bound on heap size. Explicit state enumeration can still be
expensive; this implementation does not claim the complexity or performance
of a lazy SMT encoding. Its memoized states avoid enumerating anonymous cell
identities and all their individual partitions.

## Separation between search and checking

`src/decision/sl/BooleanHeap.cpp` searches memoized abstract states.
`src/evidence/SeparationChecker.cpp` evaluates concrete finite heaps: it
enumerates actual disjoint partitions and actual representative extensions.
Every SAT witness from the decision engine must pass this checker.
The checker links in `xolver_checkers` without any decision/search objects.
Both implementations share input validation, record normalization, the
signature vocabulary and width computation. Thus they do not constitute
fully independent proofs of the finite abstraction theorem.

`Limits` supplies a work budget and a formula-depth limit. Exhaustion,
malformed DAGs, invalid records or integer literals, and arithmetic overflow
produce Unknown / an absent evaluation result. They cannot become false
semantic judgments or UNSAT. Search exhaustion over the complete finite
abstraction may return UNSAT, but no serialized UNSAT derivation or C++
refinement proof is exported yet.

The new tests cover negative star partitioning, `and` versus `star`, nested
wand laws, fresh locations and records, the singleton record domain, nil,
aliases, exact cardinalities and malformed/limited checks. The negative-star
example is also a regression shape from the primary
[cvc5 issue #12913](https://github.com/cvc5/cvc5/issues/12913).
An external corpus generator emits original SMT-LIB formulas and complete
SAT heap pins for cvc5 checking; oracle agreement is testing evidence, not
formal verification.

R17 is retained as a failed server build: an unqualified helper `advance`
selected `std::advance` through argument-dependent lookup. The helper is
renamed `nextChoices`. A test's unsupported `+7` input is corrected to the
documented decimal literal syntax. R18 passes 1576 unit tests (528788 assertions),
827 regressions, 52 tool tests, the standalone evidence binary, the architecture
check and frozen-input integrity verification. All seven suite return codes
are zero.

The R18 external run has 240 formulas, 164 SAT models and zero Xolver Unknowns.
cvc5 1.3.4 (`f3b21c4`) agrees on 232 formulas, returns Unknown on seven and
disagrees on one. It accepts 161 of the 164 pinned heaps, returns Unknown on
three and rejects none. This strict differential job is retained as failed.
Its address sort was uninterpreted; a subsequent corpus makes the infinite
address-domain assumption explicit using Int, while adding no address
arithmetic. No disagreement is classified as an oracle error on the strength
of the initial domain-ambiguous comparison alone.

For the disputed shape `(false -* p) -* p`, with p a singleton points-to,
the [archived R4 proof](evidence/sl-core-r20/formal-sl-r4/SeparationLogic.v)
proves unsatisfiability on infinite natural-number
addresses with finite heaps. The inner wand is true. Two fresh addresses always
provide a disjoint extension making the union too large for p. Coq compilation
and independent `coqchk` replay pass for these three new theorems and the six
earlier arithmetic/equality theorems, all closed under the global context.
This is a mathematical proof about the stated heap semantics, not a verified
translation of the SMT-LIB input or a C++ refinement result.

The later implementation excludes unreachable formula nodes from the location
and record vocabulary, avoiding irrelevant equality-partition enumeration.
It charges state widths and concrete heap-copy sizes against the explicit work
budget, rather than counting recursive calls alone. Validation for these later
changes is recorded separately.

R20 passes the 55-test preflight, including a 1000-unreachable-symbol case,
with 15822 passing assertions. The full suite then passes 1577 unit tests
(528793 assertions), 827 regressions and 52 tool tests. The standalone checker,
architecture checks and integrity verification of all 907 frozen inputs also
pass; all seven suite return codes are zero. All 240 original assertion structures are
identical to R18; only the address-domain declaration changes from an
uninterpreted sort to an Int alias. All 240 Xolver verdicts are unchanged.
cvc5 now agrees on case 27 as UNSAT: the original disagreement must not be
reported as an established cvc5 bug. Overall there are 233 agreements, seven
oracle Unknowns, zero disagreements and zero Xolver Unknowns. Of 164 SAT
models, 161 are accepted by the oracle, three are Unknown and none are rejected.
The strict differential job remains failed because the oracle checks are
incomplete; the Unknowns have not been relabeled as successes.

These are library-API tests. The R20 main CLI binary is byte-identical to R16,
because the new SL entry has not yet been connected to its parser/runtime.
The R20 SL corpus executable SHA256 is
`376211545e666004ec47b1d8df6047c0cac6353b39704c182da9023b4bffa60c`;
the unit executable is
`5dcd529f775fd0cf7a390d40e97fc723351a714d865e4774d2a5230e6da9ac7d`.
The source overlay SHA256 is
`cd753ff416f9173d8892c566cb4487c630703857cdd5bcf14b6a81d55ad9f40e`.
At R20 submission, all 730 C++ source/header files recorded by that manifest
matched the local working tree. Subsequent native integration changes require
their own source manifests and validation.

R20's next integration boundaries were native SL node kinds and `declare-heap`
handling in SOMTParser, then an SL dispatch before ground preprocessing and
quantified-PA routing in `Solver_impl_checksat.cpp`. That dispatch must retain
the input's location-domain semantics. A finite bit-vector address domain
cannot silently use the infinite-address completeness argument above.

## Native SMT entry (R22)

`decision/sl/NativeSeparation.cpp` reads SOMTParser nodes directly. It neither
includes `NativeTerms` nor constructs `TermExpr`. SOMTParser owns native
`sep.emp`, `sep.nil`, `pto`, `sep` and `wand` nodes and one typed heap signature.
The runtime dispatches heap queries before PA routing and ground preprocessing,
including empty queries and assumption roots.

The implemented base signature is `(Int Int)` with integer equality/disequality,
free Boolean variables, all Boolean connectives, lets and arbitrary nesting of
spatial operators. Symbolic integer data can share variables with addresses and
pure equalities. Arithmetic expressions, quantified SL, SIDs, finite domains and
uninterpreted location sorts return explicit Unknown. The infinite-domain
abstraction cannot establish UNSAT for an arbitrary uninterpreted SMT sort.

Integer constants receive pairwise disequality constraints. After the SL core
finds a heap, a finite injective renaming anchors each literal at its exact
integer, chooses unused integers for the other classes, and interprets nil
independently of integer zero. A separate evidence checker validates that
renaming, the scalar bindings, nil, every exported cell and the spatial formula.
This gives concrete checked SAT evidence; it is not an UNSAT derivation or a
formal proof of the translator or C++ implementation.

The heap lives inside the query's model, so push/pop, assertions, reset and
failed/unknown queries cannot retain a separate stale heap cache. The public
`Model::heap()` accessor, CLI heap output, spatial `get-value` and model
validation use that interpretation. Ground proof exporters are bypassed for SL
until they have an appropriate spatial proof translation.

R21 compiled on Panda1 but its preflight failed two tests because the parser
did not recognize `QF_ALL`. R22 adds that logic name, and fixes
the discovered script-reset/scope bugs: reset clears symbol declarations;
reset-assertions clears the stack, retaining declarations only with the typed
`:global-declarations` option; pop underflow is rejected without changing state.
Heap declarations survive reset-assertions and are released by full reset.
These lifetime rules follow the
[SMT-LIB standard](https://smt-lib.org/papers/smt-lib-reference-v2.7-r2025-07-07.pdf)
and the [cvc5 SL extension](https://cvc5.github.io/docs/cvc5-1.3.4/theories/separation-logic.html).
R22 passes 1583 unit tests, 833 file regressions, 58 tool tests, the standalone
checker and architecture checks, and integrity verification of all 915 frozen
inputs. Its 240-input native CLI replay agrees with the R20 library on every
case and with cvc5 on all 233 definite comparisons. Seven oracle Unknowns remain.
All 164 exported heaps are pinned back into their original input: cvc5 accepts
163 and returns Unknown on case 236. None is malformed or rejected.
The strict differential run retains failed status because of these skips.

Coq R6 changes the mathematical address domain from nat to Z, matching the
native `(Int Int)` query, and checks the additional wand laws and the case-236
model. Its theorem `case236_iff_non_nil` characterizes the original spatial
formula at nil=0; `native_case236_empty_model` proves the exported x=1/empty-heap
instance. The proof uses quantification over all finite integer heaps, rather
than the C++ decision procedure's finite representatives. Both coqc and coqchk
pass; all 13 printed theorems (seven SL, six earlier arithmetic/equality) are
closed without additional axioms. The initial R5 tactic failure is preserved.
The SMT-to-Coq specialization remains manual, and does not verify the parser,
integer renaming, finite abstraction theorem or C++ program.

The [R22 validation report](VALIDATION-NATIVE-TERMS.md#native-sl-entry-and-model-evidence-r22)
and [evidence manifest](evidence/sl-native-r22-evidence.tar.manifest.json) record
the exact input/model/proof hashes, successful runs and failed attempts.

The [evidence manifest](evidence/sl-core-r20-evidence.tar.manifest.json) binds
2715 archived records, all verified after download. Archive SHA256:
`d973b8338a8905a0625f9c58c43c3ed5bb856468ed70890947c25b58d337f315`.
The [domain comparison](evidence/sl-core-r20/sl-domain-comparison.json) records
all 240 source pairs and the manual specialization of the Coq theorem.
The [EOS index](evidence/sl-core-r20/sl-core-r20-evidence.tar-eos-runs.json)
retains both successful and failed runs. Native R18/R20 and formal SL R4 are
terminal successes; R17 and both strict differential jobs are terminal failures
for the reasons documented above. The Coq compiler is version 8.20.1;
`coqc` and `coqchk` both return zero and report nine closed theorems.
