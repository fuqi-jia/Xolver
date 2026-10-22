# Native formula ownership and typed configuration

This work replaces the duplicated expression graph with SOMTParser DAG handles
throughout the solver. Native R12 passes the server unit and regression suites;
the earlier R9 results in `VALIDATION-ARCHITECTURE.md` concern a different source
state. New proof-replay fixtures subsequently exposed three parser
counterexamples outside those tests. R14 fixes them and passes 1564 unit tests,
823 file regressions and 200 syntax/expansion pairs against both oracles.
R15 adds mixed Boolean/integer quantification and piecewise integer terms;
R16 fixes the additional Boolean distinctness bugs exposed by new differential
tests, with 1567 unit tests, 827 regressions and all 180 new expansion pairs
passing. The 45-claim independent PA proof replay is documented in
[PA-ISABELLE.md](PA-ISABELLE.md).
The migration-specific results and remaining failures are recorded in
[VALIDATION-NATIVE-TERMS.md](VALIDATION-NATIVE-TERMS.md).

## Representation

`NativeTerms` stores native shared pointers, an identity-to-index table, native
sort references, scoped assertion indices and theory metadata. It stores no
`TermExpr` graph and no second expression hash-cons table. `TermExpr` is a
temporary construction/read value. Arithmetic, EUF, array, datatype, Boolean,
model and ground-proof consumers still use this compatibility index. The R23 PA
implementation and the native SL entry consume SOMTParser nodes directly and
construct only their own theory representations. Parsed queries retain
their native nodes; programmatic construction creates native nodes directly.
The separate quantified-PA index and the lazy conversion API path are removed.

The construction contract is:

- Index original nodes by object identity, with children before parents.
- Resolve let aliases by their binding nodes, never by printed names.
- Preserve bound-variable declaration identity, including shadowed names.
- Complete nodes before registration; there is no mutable `get()` reference.
- Shared construction uses SOMTParser structural equality. Equal constants can
  share across distinct construction handles; different bound declarations
  cannot. Scope state and native-node identity are distinct concerns.
- Parser `IntOrReal` numeral placeholders are resolved bottom-up once, retaining
  rational values and Real division. The native DAG itself is unchanged.
- Construction requires a registered native sort. Array/BV/FP/datatype sorts
  require their parameters, not just an opaque kind tag. Ground lowering
  registers its possible Bool/Int/Real output sorts before introducing witnesses.

The old `CoreIr`/`CoreExpr` classes and their implementation header are removed.
The architecture check rejects their reintroduction. Source-move preimages are
recorded in `architecture-migration.json`; historical reports remain historical.

Native DAG operations required fixes beyond changing solver interfaces:

1. `NodeManager::clear()` used to clear the children of nodes still held by
   external owners. It now releases only manager references.
2. Recursive `shared_ptr` destruction of a deep native DAG can exhaust the
   process stack. Node destruction now drains a per-destruction work queue;
   nodes with remaining owners retain their contents.
3. Structural equality also recursed through native DAGs. It now uses an
   explicit pair worklist and visited pairs, including shared subgraphs.

The migration also exposed a pre-existing stack-reference lifetime error in
Boolean subterm purification: reading the parent frame after pushing a child
could read freed vector storage. Context is now copied before stack growth.
The memo key includes formula/argument context, so first visiting a shared
Boolean expression as a formula does not suppress its later purification in a
UF argument. Wide-formula and both-visitation-order tests cover these cases.

The UF-to-arithmetic purifier also distinguishes usage contexts. It handles
every operand of n-ary arithmetic and determines the arithmetic nature of an
equality from its operands, since the equality itself has Boolean sort.
SOMTParser operator names are preserved during shared construction so a
reconstructed operator can reuse its original parser node.

Polynomial predicate identity is now defined by exact coefficients rather than
`PolyId` allocation identity. The algebra layer normalizes nonzero scalar
multiples, inequality orientation and complement polarity. The SAT adapter
equates the corresponding literals while retaining the original theory
records. This normalization does not itself close the remaining NRA timeout.

The independent evidence checker links the native IR/numeric library,
`somtparser_ir`, without the parser frontend, SAT search or polynomial search
backends. The same IR object files are reused in the complete parser library.

## Configuration semantics

The 61 former textual controls now have explicit Boolean, diagnostic-presence,
integer, filesystem-path, profiling-destination, sampling-period, capacity,
modulus-list or projection-enum types. No production consumer receives a raw
configuration string through `config::read`.

Behavior changes are deliberate and require regression validation:

- Newly classified Boolean controls recognize case-insensitive `true/false`,
  `yes/no`, `on/off`, and `1/0`. Empty or malformed input uses the caller's
  default. Historical arbitrary strings and first-character tests are retired
  for these controls.
- `NIA_ZOHAR_PLUGIN=0` no longer disables a different preprocessing stage while
  leaving the plugin itself disabled.
- Diagnostic presence controls retain their documented presence semantics.
  Paths are owned values and may contain spaces. A path is not parsed as a
  Boolean switch.
- `ARITH_STAGE_PROF` is an optional destination: missing/false disables, true or
  empty selects the default path, and other strings supply a path.
- `DECIDE_PROBE=0` disables sampling, `1`/true uses a period of 2000, and a
  positive integer greater than one selects that period. Negative, malformed
  and overflowing values disable sampling.
- `SAT_LEMMA_MGMT` is an entry capacity: zero disables eviction, a positive
  integer is the capacity, and true selects 100000. Invalid values are zero.
- The modulus list must consist entirely of integers in `[2,100]`; duplicates
  are removed. Invalid, overflowing or trailing-comma lists use the documented
  default set rather than silently accepting a prefix.
- Projection selection is the enum Automatic/Collins/Lazard.

Eight duplicate declarations with identical types are merged. Obsolete key
suffixes are removed. `PP_LET_ELIM` is retired: native let resolution is a
binding operation and does not have a feature gate. The resulting catalog has
404 controls at 530 read sites, with zero textual controls. Existing separately
typed `Flag`, `Presence` and `ExactZero` compatibility policies outside the
61-control migration remain explicit in the catalog.

`XOLVER_NRA_CAC_ALL_EFFORTS` is also retired. The arithmetic pipeline has an
explicit `ReasonerSchedule`: propagation checks and candidate-model checks.
Unrestricted nonlinear covering/projection and algebraic model construction
are assigned to candidate checks. Full checks still require theory validation;
an absence of conflict during partial propagation cannot establish SAT.
This scheduling change is included in the R12 regression and performance checks.
`XOLVER_NRA_CAC_EARLY_INFEAS_SAFE` is removed as dead configuration: it only
copied a value into an unread engine field. The old comment describing an
additional correctness fix did not correspond to any executed code.

`XOLVER_NRA_LINEAR_SUBSET_UNSAT` is retired. The early exact simplex check now
relaxes every supported polynomial monomial to an independent real variable.
A contradiction in that weaker system proves an original conflict; a feasible
relaxation never establishes nonlinear satisfiability. The implementation also
distinguishes the simplex's `Unknown` result from `Unsat`, rather than treating
every non-`Sat` result as a contradiction. These changes are covered by the
R12 tests; they do not by themselves prove nonlinear decision completeness.

## PA scope and total definitions

Native R15 extends the exact PA path to Boolean quantifiers and integer
`ite/abs`. A Boolean value is represented by an integer restricted to `[0,1]`.
For a universal Boolean binder the implementation restricts the existential
counterexample to that domain before elimination; it does not universally
quantify over all integers or register bound Booleans as free model symbols.

Integer piecewise terms use fresh variables with total, unique defining
relations. These definitions can be shared through negation and other Boolean
connectives within a scope. They are existentially closed before eliminating
the surrounding user binder. For example,
`forall p:Bool. exists x:Int. x = ite(p,3,-2)` is true, whereas moving the
integer witness outside `forall p` makes it false. Constant-divisor quotient
definitions follow the same scope rule. The native implementation caches
piecewise definitions by DAG identity within each scope.

These are implementation contracts covered by mixed-quantifier tests and
independent result replay; they are not a general refinement theorem for the
C++ transformations. Free-variable models are reconstructed from projected
constraints. Full native quantifier-elimination certificates remain open.

## Presolve expansion and explanations

R11's focused NRA run returned `unknown` after roughly 22 seconds. Its verbose
profile identified a caught allocation failure in polynomial definition
substitution: 49 of 53 samples traversed presolve substitution, despite its
nominal 50 ms deadline. The 256-term check covered only the defining polynomial,
not its expansion into the remaining atoms.

R12 prepares substitutions before committing any state. It checks a conservative
expanded-monomial bound and exponent representability, and observes the existing
deadline between rewrites. Declining a rewrite retains the defining equality.
Forward and backward substitution composition now include every source fact in
the derivation ledger; composed facts receive new indices rather than inheriting
the old, incomplete explanation. This repairs premise provenance, not just cost.

The duplicate presolve polynomial-substitution function is removed in favor of
the algebra implementation. That implementation reuses repeated powers and
normalizes the accumulated sum once. Binary powering no longer computes an
unused last square, which could overflow an exponent even when the requested
power fits. Exact monomial relaxation now precedes presolve and returns the
simplex conflict's premises rather than the whole active assignment.
R12 passes all 820 file regressions and 1562 unit tests. The additional
320-case nonlinear differential run found no wrong results, but recorded nine
candidate timeouts. Full results and source/binary hashes are in the validation
report.

## SL heap search and arithmetic combination

`decision/sl/HeapSearch.h` separates heap search from choosing the stack's
equality arrangement. `solveHeap` takes a prepared SL formula, a fixed mapping
of location symbols to abstract values, and a caller-owned work budget. It
preserves that mapping, including nonconsecutive values, and searches only the
heap. UNSAT rules out the supplied arrangement; the existential entry point
continues with other arrangements. Invalid stacks and exhausted resources
cannot be interpreted as UNSAT.

Formula preparation can be reused across candidates. Heap search and independent
model checking consume the same budget. The existing equality-only entry point
uses this interface, so there is one implementation of heap search. Tests cover
nil, aliasing under magic wand, repeated calls, insufficient checking budget,
and agreement with concrete heap enumeration for each generated stack.

R27 introduced this interface; R28–R33 connect the native PA and SL paths.
`NativeArithmetic` reuses native arithmetic DAG nodes, creates fresh definitions
for shared terms and heap-independent predicates, and replaces nil with one free
integer symbol. It obtains a PA model, searches its equality arrangement for a
heap, and excludes a rejected class of stacks before trying another model.
That class fixes explicit pure relations, address/nil aliasing and equality
between mentioned records. Data/address cross-equalities are retained when the
formula explicitly observes them. Other cross-equalities cannot affect the
finite heap abstraction and do not require separate candidate enumeration.

Blocking clauses are constructed directly as disjunctions. Negating a fully
expanded conjunction of disequalities first had produced exponentially many
intermediate arithmetic cubes. Necessary stack conditions also track mandatory
allocations and exact singleton heaps through Boolean polarity. Star requires
disjoint mandatory addresses; conjunction requires singleton heaps to agree.
A heap-independent wand antecedent admits the empty extension, allowing useful
necessary conditions without treating a spatial antecedent as a pure atom.
Unsupported domains, nonlinear terms, spatial binders/SIDs and
heap-dependent arithmetic conditions remain UNKNOWN.

PA can now supply its free-variable DNF and exact assignments to a separate
arithmetic model checker. SL checks those constraints as well as the binding to
the exported integer heap. Arithmetic `get-value` pins the existing source
variables and nil instead of choosing a new interpretation. Import, search,
theory calls and checking share the work budget; SL also observes the solve
deadline. Heap search distinguishes only points-to addresses, while the
independent checker retains the larger stack vocabulary.

The PA eliminator substitutes a variable fixed by opposite affine bounds before
enumerating residues. Scaling preserves the corresponding divisibility
constraint for non-unit coefficients. Model reconstruction likewise checks a
unique integer fixed by its interval directly. These rules use the existing
elimination trace and independently checkable model representation.

Server validation separates the original mixed-nil corpus from a second corpus
that explicitly fixes nil to zero. It also replays 240 historical Boolean SL
formulas through arithmetic variable shifts. The installed cvc5 1.3.4 has a
reproduced inconsistency on an unconstrained-nil example: the original query is
reported UNSAT, while adding the exported nil binding makes it SAT. The raw
disagreement is retained as a failed strict differential check. The
[validation report](VALIDATION-NATIVE-TERMS.md) records the exact source revisions,
completed suites and model checks; no global performance improvement is inferred
from these bounded semantic tests.

## Required evidence still outstanding

The validation report records compilation, unit/regression, differential,
Python, standalone checker and performance evidence by source version.
The measured solver performance comparison does not establish a
significant speedup, and the remaining unknown/timeout cases stay open.
Subsequent source changes require their own evidence.
PA certificate coverage and full SL support remain solver requirements. Per the
user's scope clarification on 2026-10-21, formally proving the input translator,
composition of native transformations or C++ implementation is not a delivery
requirement. Correct SMT semantics, verdicts, models and reproducible validation
remain required; optional proof replay supplements solver testing.
