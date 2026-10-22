# Bugs deferred until gate cleanup is complete

The user's latest instruction is to delete all gates first, then investigate and
fix remaining bugs. These reports are retained without claiming reproduction or
source attribution:

- Existing local-main binary reportedly disagrees with Z3 and cvc5 on negative
  mod inputs. Exact testcase, binary revision/hash and source correspondence have
  not been verified in this continuation.
- Existing local-main binary reportedly omits answers from a multiple-check-sat
  script. Exact script and output sequence remain to be verified.

Preserve reproduction files when located; use Panda1/ExperimentOS for solver runs.
The confirmed bilinear scoring lifetime defect is documented separately in
`evidence/gate-0048/lifetime-README.md`; its unused implementation is removed
within gate batch01, without opening a separate general bug-repair workstream.

## Model checks reproduced during batch01 validation

Generated seed 17001 inputs 080 and 090 return SAT in ordinary solving in both
pre-removal step47 and batch01. Z3 and cvc5 agree SAT. Both frozen Xolver binaries
fail strict model-check with exit 1 and "model violated or not fully evaluable".
Panda1 attribution experiment 7bc05c27e73f, run c75defff3996, confirms both baseline
failures. This does not establish whether exported models or evaluability are
at fault. Preserve original failing suite; investigate after gate cleanup.
Input hashes: 080 = 7dddac07a5cbe9348ba9f0fc6940ae688263c54ade414ca54a94578cb8b23814;
090 = 37c3e67313df5cf50a8ecba402648b9f19ec76c6767586d74f575e1c0378b070.

## Read-only array reconstruction exposed by CLI/API unification

Batch09 built successfully, but 2 of817 unit cases fail with3 failed assertions:
`QF_ALIA constant index disequality changes the integer model` (both ±1 cases) and
`NIA: combination linear model covers wide modulus values`. This is a real API
regression: frozen batch03-05 passes both unit cases and current batch09 fails.
It must not be waived as an existing unit failure.

ExperimentOS attribution23ced2dd295d/run c96d6d170ad4 checked the three formulas
through both frozen CLIs: both versions fail all3 positive model checks and emit
identical constant-zero arrays despite constrained reads. The old CLI already
enabled read-only-array preprocessing; old library defaults left it disabled.
Removing that split exposed the same missing model reconstruction to the API.

Source diagnosis: `ReadOnlyArrayElim::ReadRec` keeps scalar read witnesses;
`Solver::Impl::modelPositivelyValidates` consumes them as temporary select
overrides. They are not materialized into `TheoryModel::arrayInterps`;
`completeArrayModel` also refuses an entirely empty array model. `dumpModel`
therefore treats the eliminated constrained arrays as unconstrained and prints
zero. Fix the returned model itself, check concrete-index collisions, support
nested array paths, and validate/output that same model. Do not weaken tests or
restore the gate. Batch10 now reconstructs concrete array tables (including nested/Boolean reads), rejects index collisions, and shares the same table with public validation and model output. Batch10 passes all820 related unit cases. Eight concrete printed models pass16 Z3/cvc5 replays. Batch11 also passes828 related units and18 printed-model replays; its902-case paired validation passes without wrong answers, execution errors, regressions or model failures.

## New verdict regression after batches04–09

`tests/regression/ufdtnia/ufdtnia_002_unsat_selector_constructor.smt2` now
returns Unknown in0.09s at both6s and20s limits; frozen batch03-05 returns UNSAT.
Input SHA-2568c60baa6f0d4f4d2cf7565909b91438635aa1d05478f333b6f73a4f37a1d7586.
Formula constrains x*x=9,x>0, and fst(mk(x,y))=4. This is not resource exhaustion.
Frozen batch09 trace confirmed that batch04-06 made the former optional DT strict
indeterminacy rejection unconditional; DtModelValidator has no arithmetic
assignment and can label cross-theory indeterminacy as Violated, causing an
early Unknown before arithmetic/selector reasoning produces the conflict.
All3 assertions were Indeterminate, then promoted to Violated. Batch10 removes that invalid promotion; definite violations and structural datatype completeness checks remain. The original UNSAT regression and its SAT neighbor now pass; batch10 has zero verdict regressions in902 paired cases. Full strict evidence is gate-batch-09-results.tar.gz
(SHA-25628ec71394d3ccb8f2b770f600430b0753f4f763dbb7850ed8a795747a1b668d2,1137members verified).

## UF model reconstruction after gate cleanup

Batch10 fixes old generated090. Generated080 remained a strict model failure:
opaque function results were printed as arbitrary positive integers despite
negative arithmetic bounds. The aggregator discarded an arithmetic value when
more than one distinct e-class mapped to it. Separate e-classes do not entail
disequality. Batch11 removes that incorrect injectivity requirement, preserving
concrete arithmetic witnesses; one class with conflicting numbers and duplicate
function tuples with conflicting outputs still cannot certify a model. The new
seed080 unit passes, and all9 focused printed models (including both old failures)
pass18 independent Z3/cvc5 replays. Final batch11 validation passes:828 related units,902 paired cases,76 model checks and18 external model replays;no wrong answers,errors,regressions,model failures or unknown. Both binaries time out on6 cases.

## NRA repeated-run instability after gate batch12

All known legacy gates are now removed. The remaining validation blocker is
`tests/regression/nra/nra_194_sat_metitarski_sqrt-1mcosq-8-chunk-0290.smt2`,
SHA256 `f757bbeba4ab28da43cdf4fdd00db5839a36bc0c7144bdcc8b8ce87ed5c51774`.
Identical frozen binaries alternate between SAT in roughly0.36s and a20s timeout.
The r4 model-check failed by timeout, not by reporting an invalid model.
A separate15-attempt ExperimentOS run (7a16ff4b02d4/e259ce545b2b) recorded13timeouts
across the accepted batch11 baseline, batch12-r2 and batch12-r4. No cause has been
established; do not dismiss this as a gate-removal regression or assert it is fixed.
All attempts, binary hashes and protocols are preserved in gate-batch-12 evidence.
The final r4 suite passed833units/243658assertions and had902pairs with0wrong answers,
0errors and0verdict regressions, but1model-check timeout out of77checks, so strict
acceptance is failed. Preserve that status; do not omit the case or waive the check.
