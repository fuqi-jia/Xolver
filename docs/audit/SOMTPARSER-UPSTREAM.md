# Current upstream status (2026-10-23)

PR #62 is merged into SOMTParser main at `ac3efd64c1b6ac88fd00803f8edf33a44e499194`. Xolver pins this main merge commit. Its tree is identical to the previously validated PR head `8248739a04e57481f2bd636c080d89d3f5ba1bc4`; the submodule is clean. The review-required notes below describe the earlier state.

## Historical integration record

# SOMTParser upstream integration

Parser changes are developed in the SOMTParser repository and submitted to its
`main` branch before becoming a released Xolver dependency. An uncommitted
`third_party/SOMTParser` patch is not a deliverable dependency version.

The current integration is [SOMTParser PR #62](https://github.com/fuqi-jia/SOMTParser/pull/62),
branch `fix/native-bindings-and-recursive-symbols`. It combines the earlier native
IR/heap/binding repairs with current upstream main (`f730eaa`) and immutable
recursive declaration environments. The Xolver gitlink still names the earlier
base; the PR checkout is used for integration validation only. Once the upstream
PR is merged, select the resulting main commit, update the Xolver gitlink, and
verify a clean `git submodule update --init` against that committed dependency.
Do not force-update other submodules or discard a dirty dependency checkout.

The clean PR head is `8248739a04e57481f2bd636c080d89d3f5ba1bc4`.
[GitHub CI](https://github.com/fuqi-jia/SOMTParser/actions/runs/39562949056)
passes all 61 C++ tests and both Python jobs (3.9 and 3.12). ExperimentOS independently
passes the same 61 C++ tests with source-integrity verification. The preceding CI
failure is retained: its reset-assertions test incorrectly treated scoped
declarations as global. The repaired test checks both option settings.

The production parser sources are unchanged since R36. That integration passed
380 PA equivalence pairs (200 syntax, 180 piecewise) and 120 model cases, including
82 checked SAT models, with no disagreement, unknown, or timeout. R40 passes all
1,604 Xolver unit tests / 540,181 assertions, the standalone checker, 68 tool
tests, architecture checks, and frozen-input integrity. Its file regressions
are **840 PASS / 1 unknown** out of 841, so it is not a complete integration pass.
The 200-case combination differential has no wrong answers, errors, or timeouts,
but retains 11 unknowns. The 160-case NRA differential has 142 oracle-agreed
cases, no wrong answers, 2 Xolver timeouts, and 18 oracle skips.

Downstream repairs cover connected array defaults, integer/constant interface
disequalities, rational separation of algebraic root brackets, and CAC deadline
checks inside cell enumeration. R41 additionally forwards the eager bit-blast
allocation to each internal SAT solve; R42 removes the obsolete authorization
gate that ignored array-generated integer disequalities. R43 adapts the three
SAT test doubles to the deadline interface. Its independent server run passes
1,608 unit tests / 540,195 assertions, all 841 file regressions, the standalone
checker, tool tests, architecture checks and frozen-input integrity. Its
200-case combination differential has five remaining unknowns, no wrong answers,
errors or timeouts; the NRA counts remain 142 checked, two timeouts and 18 oracle
skips out of 160 generated cases. No parser semantics were changed to hide the
downstream failures.

The six newly solved combination inputs received a separate strict model check:
five pass, while case 125 (a nonconstant UF over arrays) returns unknown from
model validation. NRA194 also takes 150.531 seconds in R43 versus 0.344 seconds
in R40, despite ultimately returning SAT. The model issue is repaired below, while the performance issue remains open;
the passing verdict regression suite is not a complete model or performance pass.
R44 carries first-class array values through the UF model table, compares array
arguments extensionally, resolves Boolean result classes, and prints concrete
array arguments/results. All 1,612 unit tests / 540,206 assertions pass. The six
recovered cases now all pass strict internal validation and Z3/cvc5 replay of
the printed model definitions: the original formula is SAT and its negation is
UNSAT. The first cvc5 replay omitted `--arrays-exp` and failed; the separate R44b
run replays the identical saved queries with that option, retaining the failed
attempt. R44 also passes all 842 file regressions. R45 fixes open-endpoint root selection
and compares disjoint rational isolating intervals before re-isolating roots. Its
independent run passes 1,614 unit tests / 540,227 assertions, 842 file regressions,
and all six strict/printed model checks. However, the 200-case combination
differential has seven unknowns (new cases 17 and 72 relative to R43), and the NRA
differential retains two timeouts and 18 oracle skips. NRA194 takes 141.261 seconds
in R45; R44 took 0.349 seconds without an NRA algorithm change. Neither a stable
performance improvement nor elimination of the combination gaps is established.

PR #62 is now ready for review, with the same tested head. A normal squash merge
was rejected because repository ruleset `5590872` requires one approving review
and code-owner review where applicable. All three checks pass; GitHub reports
`REVIEW_REQUIRED`. Legacy branch-protection returns 404, which does **not** mean
the ruleset is absent. Auto-merge is disabled. No administrator bypass or policy
change was used. The Xolver gitlink remains at its earlier base until the PR is
merged into main; there is no released dependency update yet.

R34–R38 failures/cancellations, upstream CI/server results, PA differentials and
bounded profiling are retained in
`evidence/somtparser-pr62-integration-r1-evidence.tar.gz`, with its manifest and
`evidence/somtparser-pr62-provenance/verify_evidence.py`. Verification checks all
5,064 archived members and 18 terminal runs. A diagnostic job succeeding means
the observation completed, not that its solver succeeded.

The follow-up R39–R43 records, differentials and model failures are retained in
`evidence/somtparser-pr62-integration-r2-evidence.tar.gz`. Its manifest and
`evidence/somtparser-pr62-provenance/verify_followup.py` verify 3,683 members,
2,784 frozen inputs and 11 terminal runs. `verification-followup.json` explicitly
records the model failure and the NRA194 timings; it does not label this a
complete integration pass.

The R44 full-suite and array-model records, including the first cvc5 replay
configuration failure, are retained in `evidence/somtparser-pr62-integration-r3-evidence.tar.gz`.
`verify_array_models.py` verifies 1,155 members, 929 frozen inputs and three terminal runs.
R45 full-suite, model and differential records are retained separately in
`evidence/somtparser-pr62-integration-r4-evidence.tar.gz`. `verify_r45.py` verifies
1,338 members, 929 frozen inputs and three terminal runs, and explicitly retains
the seven combination unknowns, NRA timeouts and NRA194 slow result.

R46 passes 1,619 unit tests / 540,288 assertions and all 842 file regressions
for NRA candidate scheduling, interface-aware witness checks, nonzero RHS
forwarding and scope/trail/model lifetime repairs. Its differentials retain seven
combination unknowns and two NRA timeouts. Frozen-binary diagnostics show cases
17 and 72 also failed strict model checking in R43 despite its SAT verdicts.

R47 additionally repairs binary negated-distinct array completion and LRA delta
materialization across asserted disequalities. It passes 1,621 unit tests /
540,308 assertions, all 843 frozen file regressions, the standalone checker,
tool tests, architecture and input integrity. The 200-case combination differential
now retains three unknowns (17, 101, 116), without wrong answers, errors or timeouts.
The NRA differential retains two timeouts and 18 oracle skips. Ten models pass
strict checking and 40 independent Z3/cvc5 observations: the six previously
recovered models plus cases 72, 10, 106 and 174. The last three are also retained
as permanent regression fixtures with matching hashes; they were checked in the
separate model run and are not counted in the frozen 843-case full suite.
The initial seven-model EOS run is retained as invalid because its expected-count
check still required six. A separate successful record-verification run corrects
that check without changing or rerunning the recorded solver outputs.

R46 full validation, differentials and the old-binary gap diagnostics are retained
in `evidence/somtparser-pr62-integration-r5-evidence.tar.gz`. `verify_r46.py`
verifies 1,352 members, 929 frozen inputs and five terminal runs, including the
18 repeated verdict observations and four unsuccessful strict-model observations.
NRA194 remains slow at 141.806 seconds in R46.

R47 full validation, differentials, model replays and the corrected-count audit
are retained in `evidence/somtparser-pr62-integration-r6-evidence.tar.gz`.
`verify_r47.py` verifies 1,356 members, 930 frozen inputs and five terminal runs,
including the invalid first model-run metadata. The archive hash is
`f4e416996a6b9f5e3a086f494d9bd35c8778f4d15406e8ce8aecdd81552f1422`.
NRA194 remains slow at 138.954 seconds; no global speedup is claimed.

The source packager now includes committed submodule changes relative to the
superproject pin, rather than only uncommitted files. Removed upstream files carry
verified preimage hashes. The immutable source overlays and manifests are
in `evidence/native-source-overlays`; build writers share the persistent Panda1
build directory and its lock. No new complete build tree was created.

This integration does not complete quantified spatial solving, recursive SL
search, all solver certificates, control cleanup, or the global performance
comparison. Those remain requirements of the active solver work.
