# PA completion work (parallel overlay, 2026-10-22)

The PA implementation is integrated and its targeted Panda1 validation passed.
All PA tests in the combined native0002 unit selection passed; its three failed
SL tests are recorded separately. The corrected external adapter passed 109/109
original-input verdicts and certificate schemas, 218/218 independent oracle
verdicts and 11 original-formula model pins, with no wrong answers, Unknowns or
incomplete checks in that targeted suite. The first indexed-syntax oracle
failure is retained; no parser error is counted as a rejected model.

The broader 200-case differential suite still has 11 candidate Unknowns and five
oracle-incomplete checks, no wrong answers/errors/disagreements. A separate
120-case model suite checked 73 models, with no Unknowns or rejected models.
This does not establish full-corpus success or a general speedup.

Isabelle run `0a66c5eb33a8` accepted all 27 claims, 50 actual QE obligations and
four model claims, and rejected both a falsified inner step and a falsified
model. Proof input and solver hashes were verified. The earlier 8G startup
failure, 32G pure-Presburger timeout and partial-simplification proof failures
are preserved. The final method tries a simplification that closes the whole
claim, otherwise replays Presburger on the original goal. Every theorem still
passes the no-oracle-dependencies check. No goal is weakened or skipped.

## Existing and proposed semantic coverage

The existing decision procedure is Cooper elimination over exact GMP integers:
Boolean combinations, arbitrary alternation of Int/Bool quantifiers, free symbols,
affine addition/subtraction and constant multiplication, comparisons and
(distinct/equality) chains, simultaneous let aliases, nonzero constant Euclidean
div/mod, integer ite/abs and Boolean ite/xor/implication. Bound variables use
SOMTParser declaration identity. Models are reconstructed through recorded free
projections; optional evidence records every completed existential QE equation.

This patch fills two native language gaps:

- `((_ divisible n) t)` becomes a PA divisibility literal. The standard restricts
  `n` to positive numerals; a native zero/nonpositive modulus is rejected without
  a verdict or certificate. No zero-modulus reinterpretation is introduced.
- Native n-ary integer div follows left-associative Euclidean semantics. A signed
  chain is folded to one quotient witness using exact integer arithmetic. If
  `s*floor(N/M)` is the current value, the next positive division retains `N`
  when `s=1`, and changes it to `-N+M-1` when `s=-1`; the new denominator is
  `M*abs(d)` and the outer sign is `sign(d)`. Quotient keys distinguish a folded
  chain from a binary division whose dividend is that chain.

The independent Isabelle translator now handles the same indexed predicate and
left-associative signed division. These semantics follow the official
[SMT-LIB Ints theory](https://smt-lib.org/theories-Ints.shtml), specifically its
positive divisibility indices, `div :left-assoc` and Euclidean remainder rule.
The latest Ints signature also contains nonlinear exponentiation; that is not a
Presburger operation and is outside this solver's PA fragment.

**Parser prerequisite remains:** at SOMTParser revision
`8248739a04e57481f2bd636c080d89d3f5ba1bc4`, `Parser::mkDivInt(vector)` can construct
n-ary div but `src/frontend/expr_parser.cpp` still rejects textual arity > 2.
No third-party source is modified here. Native public vector-API regressions
exercise PA support now. The remote drivers list their six textual n-ary cases
as pending by default; `--include-nary-div` makes them required after an upstream
PR is merged to main and the submodule is updated. The actual C++ and Python
coverage counts must be reported separately from these pending CLI cases.

## Numeric conjunction kernel

`decision/pa/UnaryArithmetic.h` is a parser-independent exact arithmetic kernel
shared by numeric QE and free-variable model reconstruction. It is not another
general IR. It consumes the existing PA literal representation and a work/deadline
charging callback.

1. Inequalities give an exact interval with signed floor/ceiling division.
2. Each positive congruence is reduced by gcd; generalized CRT intersects the
   resulting classes, including non-coprime moduli and negative coefficients.
3. Write every candidate as `x = r + M*k`. Negative congruences exclude exact
   classes of k. Disjoint classes disappear; excluding modulus 1 is a conflict.
4. Inclusion/exclusion represents the characteristic function of allowed k as
   signed congruence classes, coalescing equal intersections. The count in an
   interval is the sum of signed differences of floor quotients.
5. One complete period suffices for an unbounded direction; a bounded interval
   may be shorter. Exact counts permit binary search for a witness without a
   numerical magnitude bound or a loop proportional to the modulus.

The numeric path is complete for a finite conjunction of one-variable affine
inequalities and positive/negative congruences. Work can be exponential in the
number of exclusions; it is charged to the ordinary work/deadline budget. The
residue budget still limits the general symbolic Cooper enumeration, while this
path performs no residue enumeration. Large moduli are therefore not by
themselves a reason to return unknown.

A QE cube uses this path only when all literals depending on the eliminated
variable contain no other variables. Independent literals survive unchanged.
General symbolic cubes retain Cooper elimination. Model reconstruction first
substitutes later projection values and uses the same numeric kernel, then
checks the resulting witness against the original projection cube. Every QE
path still passes through the same obligation-recording wrapper.

## Unknown and unsupported branches

For well-formed inputs in the listed PA fragment, the implemented elimination is
complete without resource limits. Default work/residue/depth and wall-clock limits
can still produce unknown. Variable-id exhaustion is also a resource limit.
A numerical constant's magnitude does not introduce an ad hoc finite search box.

These non-resource branches remain explicit:

- Nonlinear products, variable divisors and division/modulo by zero are outside
  the supported PA fragment. In particular, SMT-LIB zero division is an
  underspecified total function, not an integer constant to invent.
- Real, BV, array, heap, string, datatype, nonzero-arity UF and recursive-function
  operators are outside the PA backend; separate theories or expansion must
  handle them. Nonrecursive definitions work when the frontend expands them;
  raw function applications do not become affine atoms automatically.
- Ill-sorted/invalid numerals, malformed arities, nonpositive indexed moduli,
  null/cyclic aliases, invalid binders and ambiguous same-name free identities
  are malformed native inputs, not hard PA instances.
- Residual unbound variables, failure to close a formula, incomplete projection
  values, projection-order mismatch, failed witness checks and failed model
  reconstruction are invariant-failure defenses. Their occurrence on a valid
  PA input is a bug to fix, not an accepted explanation of algorithmic hardness.

A completed SAT decision can survive model-budget exhaustion with an explicitly
unavailable model. This does not fabricate an assignment or certificate. The
trace is optional, contains mathematical obligations rather than trusted proofs,
and is independently replayed with Isabelle. `checkModel` checks the projected
free formula, not the original quantified input in isolation. A replay proves
all supplied QE obligations and separately the original input/model claim.
No C++ refinement proof or independently proved input translator is claimed or
required by the user's current SMT-only scope.

## Prepared verification

- Existing and added `native PA*`/`PA reconstructs*` C++ regressions: indexed
  predicates, non-coprime CRT, covering negative congruences, exact interval
  endpoints, 30-digit moduli, large negative witnesses, resource rejection and
  independent model-evidence checks. There are 480 bounded native-query cases
  compared with direct integer enumeration, plus 160 arithmetic-kernel cases
  with up to six interacting congruences. Native vector construction checks
  signed n-ary division and big integers without depending on the parser fix.
- `tools/remote/test_pa_completion.py`: 109 required core CLI cases (96 generated
  bounded cases), two external oracle comparisons per case, actual QE artifact
  schema checks and original-formula model pins checked by both oracles. Six
  textual n-ary cases become required with `--include-nary-div`. An optional
  frozen baseline records actual before/after differences.
- Extended `tools/remote/test_pa_certificates.py`: existing independent Isabelle
  acceptance and deliberately false-step/false-model rejection, plus indexed
  predicates, CRT and negative-congruence coverage. Signed n-ary/big-integer
  replay cases are separately enabled after the parser prerequisite.
- Local lightweight verification: 11 Python translation-boundary tests pass;
  all 115 proposed CLI formulas translate to HOL and have unique case names.
  These checks do not constitute C++ execution, SAT validation or kernel proof.

All Xolver C++ builds and solver/oracle/Isabelle runs are submitted by root through
Panda1/ExperimentOS, reusing the locked persistent build and Isabelle cache.
Targeted results are above; neither full-suite success nor a performance speedup
is asserted by this checkpoint.


## Upstream n-ary division validation (2026-10-22)

The independent arithmetic frontend change is now draft
[PR #63](https://github.com/fuqi-jia/SOMTParser/pull/63), based on main `f730eaac`
with head `7e7cc94b47c0a4b208a59045f0b9d98592a11829`. It is separate from PR #62.
Panda1/ExperimentOS run `77fafeb376a7` accepted success: unpatched main reproduced
the same new regression failure; existing arithmetic controls passed; patched
focused tests and all **60/60** C++ tests passed. GCC 13.4 Debug with warnings as
errors was used. GCC 15 exposed a separate pre-existing missing `<cstdint>` include
on main; that failed build is preserved rather than attributed to this patch.

The independent source and locked persistent build live under
`/pub/data/jiafq/somtparser`. No Xolver build, third_party source or gitlink was
changed. Exact source hashes, all failed attempts and successful logs are in
`docs/audit/evidence/somtparser-nary-div/somtparser-nary-div-evidence.tar.gz`;
SHA256 `6f5bc6f5f3f22d146c833fde001c382de9b511edbbfc5b7e3a5f6f0b856301da`,
86 entries, individually verified after download. The draft must be reviewed and
merged to main before downstream submodule integration and the six additional
textual n-ary PA/Isabelle cases can be claimed as integrated coverage.

PR #63 remains draft/open at `7e7cc94b`; all three GitHub CI checks (C++, Python
3.9 and 3.12) passed. No merge or downstream gitlink change was performed.
