# Arithmetic validation and continuation record

This is an operational handoff and an evidence index. Current capabilities and
API contracts are described in [the architecture reference](../ARCHITECTURE.md),
[application interfaces](../../src/applications/README.md) and
[proof tooling](../../tools/proof/README.md). Experiment results below apply to the
named source snapshots and binaries; they do not establish general completeness
or performance superiority.

Application API continuation: [PR66](https://github.com/fuqi-jia/Xolver/pull/66)
groups SAT/SMT under `satisfiability`, MaxSAT/MaxSMT/CP/MILP/OMT under
`optimization`, PA/SL/model checking under `verification`, projected counting
under `counting`, and ODE/PDE under `dynamics`. Canonical includes and namespaces
move together; retired application paths and transition-only APIs are deleted.
See the PR for source bindings, server acceptance and CI receipts.

Optional MPI, Spark, Dask, CUDA, HIP and OpenACC execution backends all default
OFF. The runnable task protocol and worker APIs are described in
[parallel execution](../../src/parallel/README.md). Device execution verification
must distinguish OpenACC host execution from CUDA/HIP hardware execution.
This API stage makes no fixed160, protected-set or end-to-end QCP superiority claim.
The cancelled `validation/current-main.json` server archive remains unnecessary.

Earlier functional delivery: [complete GCD coverage](#complete-gcd-backend-coverage-r588r606)
([PR62](https://github.com/fuqi-jia/Xolver/pull/62)) and
[exact linear phases with a decision interface](#exact-linear-phases-and-decision-interface-r596r608)
([PR63](https://github.com/fuqi-jia/Xolver/pull/63)), combined implementation main
`db671329385edc343ada4a11a2787b9c3f903053`.
Both PRs passed their [QCP CI](https://github.com/fuqi-jia/Xolver/actions/runs/40846103315)
and [core/API CI](https://github.com/fuqi-jia/Xolver/actions/runs/40846412596).
The combined [main CI](https://github.com/fuqi-jia/Xolver/actions/runs/40849495526)
is the post-merge receipt. Documentation-only updates do not imply a new native binary.

The fresh R602 fixed160 round verifies **94** results for this implementation,
versus **95** for preceding delivered main and **115** for same-round Z3.
Z3 has 124 raw decisions; nine remain unconfirmed and are excluded. The accuracy
fix is retained under the user's explicit functionality-first instruction,
including its known SAT59 timeout regression. No performance superiority is claimed.
Older tables describe their own frozen versions and evidence boundaries.

## Current arithmetic and ASP continuation

[PR84](https://github.com/fuqi-jia/Xolver/pull/84) is merged as main `b9a15a25`.
Its exact delivery head `d753bfa5` passes both jobs of
[PR CI41169407864](https://github.com/fuqi-jia/Xolver/actions/runs/41169407864).
EOS `601c890f32c3` qualifies the final canonical comparison tool: 16 tool tests
and 243 targeted native cases pass; CLI/SV/worker/unit hashes match the 1877-case
solver qualification. Frozen delivered CLI:
`aab07fcc078c31c3aaf25b38cab9219b9cc750213357db0f0cd9cac39553e12a`.
The postmerge [main CI41170953772](https://github.com/fuqi-jia/Xolver/actions/runs/41170953772)
is still running at this evidence snapshot; its proof gate passes.

[PR85](https://github.com/fuqi-jia/Xolver/pull/85) develops shared integer
polynomial residue refutation, core `243a267f`. Reduce coefficients before
collecting variables, enumerate independent components, and retain original
SAT premises for every conflict. The bounded Boolean prepass checks explicit
integer sorts and shares the same implementation with NIA algebraic reasoning.
No integer residue rule is applied to real variables. R1115 passes 67 targeted
cases / 782 assertions. All 39 R1116 native groups pass, including 1883 unit
cases / 986681 assertions. Frozen candidate CLI:
`8dc1884e8ac2b43d3d1da45d581e42c6fd9a91df6c71a64efbad8b2bca5fbf07`.

R1120 seals a fresh fixed160 round: **101 delivered main / 101 candidate / 117 Z3
verified**, with 124 Z3 raw decisions. Both Xolver versions have 55 SAT, 46 UNSAT,
58 timeouts and 1 unknown. No gained/lost solves, opposite verdicts or invalid
models. PAR-2 is 7394.576/7381.610/5501.698s; the 12.965s single-round difference
does not establish an aggregate speedup. All timed solves use 60s, one leased
physical CPU and 16GiB, and export one initial model. Three complete triads
(45/56/140) replace observed wall-budget violations; their raw records remain.
Unconfirmed UNSATs 12/24/27/42/80/114/159 remain excluded.

The separate coupled-square regression improves 19.908s→0.068511s under the
same budgets, while Z3 and cvc5 time out. An independent direct-AST checker
validates all 81 original residue classes, proving UNSAT without using Xolver
arithmetic. The unit test changes 120.034762s→0.018012s. These are local results
outside fixed160. The published certificate and reproducible checker are
[recorded here](POLYNOMIAL_RESIDUE_STAGE_20261031.json). Final offline-checker
source qualification and exact delivery-head CI gate PR85 promotion.

R1099's preceding candidate-cache round also verifies 101/101/117 with no solving
gain. Earlier R1089 records 100→102 and legacy duplicate Z3 model exports on
32/47/108/122; those historical timings are not the current single-export round.
The R1113 early-quadratic experiment solves none of 27/34/42/116 and is closed.
No overall superiority over Z3 is established.

The original GCD pair on the earlier d80fb40b worker verifies all nine original
VCs with each backend and audits 296 actual native calls / 70 unique formulas per
backend. This does not qualify a final-kernel original multi-program QCP round.
Both independent protected sets remain unused. No extra current-main server
archive is a delivery prerequisite. Earlier named rounds describe their own
frozen sources and evidence boundaries.

The retained branches are `main`, `feat/qcp-foundations` (QCP and solver
foundations), and `feat/draco-asp`. Historical branch tips are archived in
`validation/arithmetic-r103/branch-archive-20261030/history.bundle`, SHA-256
`e318c3063355737900a6c0318a2bc6e356cbf30413b927908c7eabfe28f91971`;
the adjacent manifest maps original refs. All27 historical worktrees were
verified clean and removed at the user's request. The current repository and
Draco worktree remain. Unique `Xolver-next/validation` evidence is preserved under
the archive's `worktree-artifacts/Xolver-next/validation`; the cleanup inventory
and result record bind original paths and commits. Do not create an experimental
branch for each subsequent change.

[PR72](https://github.com/fuqi-jia/Xolver/pull/72) is delivered as main
`6802c5e4d5ddea0ef8a86614521d96bf3605c424`. Both its
[PR CI](https://github.com/fuqi-jia/Xolver/actions/runs/40959877474) and fresh,
exact-head [main CI](https://github.com/fuqi-jia/Xolver/actions/runs/40963240045)
are fully green. PR71's fresh main CI below is also fully green.

[PR71](https://github.com/fuqi-jia/Xolver/pull/71) merged consumer-directed
active context as main`61ea31ee44cf48b839e285ad888ba57d58c23bc2`, after both
[PR CI](https://github.com/fuqi-jia/Xolver/actions/runs/40956284799) jobs passed.
Its fresh exact-head [main CI](https://github.com/fuqi-jia/Xolver/actions/runs/40959749179)
is fully green.

[PR70](https://github.com/fuqi-jia/Xolver/pull/70) delivered quadratic sign refutation as main
`d8768ce172aa4c3c0f215f29f4a88fd96ac30796`. Both its
[PR CI](https://github.com/fuqi-jia/Xolver/actions/runs/40937654370) and fresh,
exact-head [main push CI](https://github.com/fuqi-jia/Xolver/actions/runs/40941544646)
are fully green. The source, frozen binary and acceptance bindings below remain
valid; no additional current-main server archive is required.

[PR67](https://github.com/fuqi-jia/Xolver/pull/67) is merged as main
`e7c7917c9a9c997a8649ad736c8548f4de186bca`, after its
[PR CI](https://github.com/fuqi-jia/Xolver/actions/runs/40899442555) passed.
The [fresh main CI](https://github.com/fuqi-jia/Xolver/actions/runs/40903458473)
is fully green. The row-snapshot stage below restores verified
fixed160 coverage from **94 to 95**, with no losses; same-round Z3 retains
**115 verified / 124 raw**. Its eight unconfirmed UNSATs and one unconfirmed SAT
remain excluded. No solver-superiority claim follows from this local gain.

[PR68](https://github.com/fuqi-jia/Xolver/pull/68), merged as `28985eac`, adds finite native ASP under
`satisfiability/asp`, reusable exact integer Boolean optimization under
`search/optimization`, and the current Draco 2 instance-local backend. Its
[first qualification](DRACO2_ASP_FUNCTION_STAGE_20261029.json) binds the latest
frozen Draco 2 source, original rules/weights/examples and real native calls:
1,771 unit tests, 102 independent ASPIF cases, 36 independently checked native
calls through three original examples, and five weighted-dependency probes.
The [first PR CI](https://github.com/fuqi-jia/Xolver/actions/runs/40898756245)
passed before rebasing onto PR67; it does not qualify the rebased combination.
The rebased server combination passes **1,772 unit cases / 877,704 assertions**
and freshly repeats all 102 ASPIF checks and 36 independently checked Draco 2
native calls. The same record binds EOS native `4b01adbd9ad0`, independent run
`6b3f8d139d31`, and `source-native-r3.tar.json`; the overlay restores the unmerged
polynomial-batching experiment. Its main SMT binary is byte-identical to frozen
R659, and its ASP binary is byte-identical to first qualification. These repeats
do not increase unique original-example coverage. The combined
[PR CI](https://github.com/fuqi-jia/Xolver/actions/runs/40905899311) and fresh
[main CI](https://github.com/fuqi-jia/Xolver/actions/runs/40909040387) are fully
green; the earlier PR CI is not substituted for them.
Grounding is forced ground-only; Xolver performs stable-model search and
optimization. Unsupported fragments fail explicitly. These are functional
checks, not a Draco or solver performance comparison. Neither protected set
was evaluated, and the cancelled current-main archive remains unnecessary.

## Delivery contract

The delivered arithmetic implementation includes:

- Exact integer interval-combination certificates and an independent exact
  verifier; polynomial equation substitution with original-model replay.
- Bounded, exact residue-table evaluation for univariate integer polynomial
  remainder identities, including large coefficients and negative divisors.
- A separation between NRA model-search exclusions and refutation evidence.
  Conclusive refutations require the corresponding certified covering evidence.
- Exact root-bracket compaction with endpoint sign checks, avoiding oversized
  dyadic evaluation intermediates while retaining the original root.
- Cached normalized local-search scores with epsilon invalidation.
- Explicit simplex backtracking policies. `AssignmentPolicy::Reinitialize`
  remains the default. LRA selects `Preserve`, retaining a row-consistent point
  and rebuilding the violation queue after withdrawing bounds. LIA root resets
  retain `Reinitialize`; integer branch-point selection depends on that policy.
- Symbolic integer remainder simplification that retains the outer `mod` when
  its divisor may be zero. Neither a zero numerator nor a nested remainder
  licenses replacing the result with zero or assuming idempotence. Term copies
  protect recursive distribution against IR storage growth.
- Integer refinement respects check effort. Standard checks retain LP/GCD
  conflicts without registering atoms for uninstalled branch lemmas. Full
  integrality checks attempt validated integer repair before cuts and variable
  branches; disequality refinements use the current relaxation model.
- Constant integer divisions expose shared remainder lattice gaps before
  branching. Relations preserve dividend identity, assertion scope and signed
  Euclidean remainders, without adding integer variables.
- Shared, budgeted integer-form projection derives affine lattice steps from
  current equalities. Disequality splits retain every equality premise, including
  theory-combination equalities; no projected state survives a context change.

The zero-divisor regressions cover `(mod d d) = 1`, `(mod 0 d) = 1`, and
`(mod (mod 7 d) d) != (mod 7 d)` with `d` chosen from `{0,1}`. All are SAT:
SMT-LIB leaves the zero-divisor function interpretation unconstrained, subject
to congruence. The differential harness checks both original verdicts and the
exported interpretation with Z3 and cvc5. Two negative controls ensure replay
rejects an incorrect or missing zero-divisor interpretation.

The qualified candidate uses clean dependency commits. Its parser change is
[SOMTParser PR65](https://github.com/fuqi-jia/SOMTParser/pull/65), whose three
CI jobs pass; required review and merge remain pending. The preceding delivered
main pins parser `49136bd1936eb34302a380a753731e577d503475`. Candidate pins are:

| Dependency | Revision |
| --- | --- |
| SOMTParser | `b9063faeab2e89d87525432eaedb8f0a5b6eb1ea` |
| CaDiCaL | `7b99c07f0bcab5824a5a3ce62c7066554017f641` |
| libpoly | `3d5e6fbd98639cb0941b029e23ca17c0e3c4a80a` |

## Server and source provenance

Panda1 is `jiafq@192.168.20.110`. The source export is
`/pub/data/jiafq/xolver`; it is not a Git checkout. Native compilation and test
execution belong on this server through ExperimentOS, not local WSL.

Use exactly one incremental build directory,
`/pub/data/jiafq/xolver/build`. Serialize writers with `build/.writer.lock`.
The arithmetic driver owns its exclusive lock; do not wrap it in a second lock.
Whole-source acceptance holds a shared lock. Frozen executables and logs belong
in `validation/`, without retaining another complete build tree.

Overlays are generated by `tools/remote/package_overlay.py`, applied by
`tools/remote/apply_overlay.py`, and accompanied by full SHA-256 manifests.
The server export base is `1d8ca5b6194b87e4b1ac81d0237f312481fecabf`.
Use `--since` with the last applied manifest so an abandoned experiment is
actually restored on the server. A build directory or binary name alone is not
sufficient source provenance.

The preceding zero-divisor qualification uses:

- Source manifest `validation/z3-gap-source-r99.json` and its matching overlay.
- Frozen executable `validation/symbolic-mod-zero-core-r99-20261026/xolver`.
- Native core qualification `validation/symbolic-mod-zero-core-r99-20261026/`.
- Whole-source acceptance `validation/full-acceptance-r100-20261026/`.
- Formal fixed-suite run `validation/z3-gap-candidate-r101-20261026/`.

Continue from the delivered Git revision, successful GitHub main CI, source
manifests, executable hashes and the existing acceptance records. An additional
server checkpoint was explicitly cancelled and is not a delivery requirement.
Source manifests can name the pre-commit working tree from which they were
packaged. Documentation-only changes do not imply a new native executable.

## Reproduction and acceptance

ExperimentOS is installed at `/pub/data/jiafq/experimentos`:

```sh
cd /pub/data/jiafq/experimentos
./eos submit -y /pub/data/jiafq/xolver/validation/focused-r99.yaml
./eos show xolver-symbolic-mod-zero-core-r99-20261026
./eos show xolver-full-acceptance-r100-20261026
./eos show xolver-z3-gap-candidate-r101-60s-20261026
```

Run names and output directories are unique evidence identities; use a new run
name when rerunning a protocol, while reusing the same incremental build.
The native driver is `validation/arithmetic-gaps-driver-r6.sh`. Acceptance runs
all unit tests, arithmetic regressions, architecture/harness checks, known-gap
contracts, independent affine and linear differential/model checks, integer
partial-function model replay, and NRA model replay. The full regression budget
is 240 seconds; differential smoke budgets are 5 seconds. These are correctness
checks, distinct from the formal benchmark budget below.

CI must pass both `build-test` and `proof-gate` on the actual delivered main
revision. A green PR alone does not establish that main CI passed. These checks
validate executable certificates and implemented contracts; they are not a
formal end-to-end proof of the C++ solver.

If ExperimentOS is pending despite free resources, refresh its configured fleet
telemetry before scheduling. Do not change the scheduler configuration or restart
its daemon to force capacity. Respect leased `EOS_CPU_IDS`, rather than assigning
multiple workers to the same physical core.

## Benchmark protocol and measured boundary

The fixed primary manifest is
`validation/z3-gap-setup-r32-20261026/fixed160-60s.json`.
Each input receives 60 seconds wall time, one physical CPU and a 16 GiB process
address-space limit. Xolver receives `--timeout 60`; solver processes also have
an external deadline. Oracle provenance is in the setup directory's
`oracle.json`: Z3 5.3.2, executable SHA-256
`44d6ba3c78204de660489b282a6b2159fafbf57813e6795ca8b2e2b83257328e`.

Primary-suite coverage before the final zero-divisor repair, on main
`7839524990dbe6f588f13e708d6a9d09e3039341`:

| Solver/snapshot | QF_LIA | QF_LRA | QF_NIA | QF_NRA | Total decided |
| --- | ---: | ---: | ---: | ---: | ---: |
| Xolver, R89 | 25 | 15 | 22 | 16 | 78 / 160 |
| Z3 5.3.2, fixed baseline | 38 | 26 | 35 | 26 | 125 / 160 |

R89 has 44 SAT, 34 UNSAT, 3 unknown and 79 timeouts; no observed opposite
verdicts, process errors or memory-limit failures on this suite. Its CLI SHA-256
is `bf87ce1df70603a05a7c950b93fb3987a7f9b17eda5591b77b2d32ff044a2efe`.
R101 is the authoritative repetition for the final repair; inspect all eight
lane reports, including `wrong_verdicts`, before using its results.

Earlier candidate coverage runs use matching immutable oracle rows from the
baseline. R109 below replaces those historical timings with a fresh paired run.
No overall claim of beating Z3 is justified. The protected
`independent160-60s.json` manifest remains unused;
do not inspect its outcomes or tune on it before a separately declared holdout
qualification.

Shared benchmark archives are immutable and referenced in place:

- WSL: `/mnt/d/D_Work/ISCAS/datasets/smtlib-2025`.
- Windows: `D:\D_Work\ISCAS\datasets\smtlib-2025`.
- Panda1 extracted inputs:
  `/pub/data/jiafq/smt-comp-2025/benchmark/non-incremental`.

The local shared archive is a partial release. Consult its README and manifest,
verify source hashes and do not copy full archives into individual experiments.

## Shared integer interval stage (R103–R112)

Delivered through [PR #42](https://github.com/fuqi-jia/Xolver/pull/42) as main
`040a3656547489f0c3daaa96d3a4de5b1a051da4`.
[Main CI](https://github.com/fuqi-jia/Xolver/actions/runs/40339177941)
completed successfully with both `build-test` and `proof-gate` green.

The source base is main `ea240d2e`. The machine-readable
[stage record](ARITHMETIC_INTERVAL_STAGE_20261026.json) contains the frozen binary
hashes, input hashes, 160 report digests, gap inventory, sampled frames and
confirmation evidence. All paths below are relative to
`validation/arithmetic-r103/` on Panda1.

The missing capability was multi-variable interval reasoning: both
`IntervalEvaluator` and the ICP factory skipped these polynomials. On primary
case 125, 44 of 49 diagnostic samples were in `NiaSolver::stageModular` while
bounded nonlinear definitions could not propagate their result intervals.
The implementation now evaluates monomial enclosures in the shared algebra
layer and projects isolatable linear coordinates in `RelationContractor`.
Cached polynomial structure avoids rescanning it on every contraction;
reason unions retain all premises without accumulating duplicates. Integer
rounding is restricted to integer owners; real owners retain sound forward
enclosures. The modular search also skips enumerations whose mandatory raw
certificate is known to exceed its verifier budget. That preflight alone did
not add a solve; it does not bypass certificate checking.

The fresh fixed160 comparison used the frozen R99 baseline, R109 candidate and
the same frozen Z3, in rotating order on each leased physical CPU, all at
60 seconds and 16 GiB. Model export and independent replay are separate untimed
correctness checks with the same per-invocation limits.

| Version | SAT | UNSAT | Unknown | Timeout | Independently verified | Verified PAR-2 total (s) |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Xolver R99 | 44 | 34 | 3 | 79 | 75 | 10432.565 |
| Xolver R109 | 44 | 35 | 3 | 78 | 76 | 10314.551 |
| Z3, fresh round | 66 | 58 | 0 | 36 | 109 | 6343.908 |

Exactly one verified solve was gained and none lost:
`QF_NIA/calypto/problem-000123.cvc.1.smt2` (index 125) changed from a
60-second timeout to UNSAT in 1.568 seconds; Z3 independently returned UNSAT
in 0.065 seconds. No opposite verdict, process error or invalid replay was
observed. Z3 returned 124 decisions this round; the earlier 125 is historical.
Unconfirmed decisions receive the PAR-2 penalty. Both Xolver versions still
lack a completed model replay for SAT indices 75 and 148 and an independent
UNSAT confirmation for index 115. Z3 has 15 unconfirmed decisions under this
strict protocol. Raw decisions must not be presented as verified coverage.

R101's ten `unconfirmed` entries meant an unknown source status without an
independent check, rather than ten established errors. All original hashes
were checked: SAT indices 20, 36, 87, 112 and 126 passed Z3 and cvc5 model
replay; UNSAT indices 18, 101 and 132 agreed with both oracles, and 41 with
Z3 while cvc5 timed out. Index 115, `ps6.c_7.smt2`, remains unconfirmed after
both independent 60-second checks. It is excluded from verified scores.

Server acceptance passed 1,655 unit tests / 794,868 assertions, 892 regressions,
architecture and harness checks, two explicit known-gap contracts, affine and
linear differential checks, partial-function replay and QCP VC checks.
The new deterministic interval differential suite passed 128 cases with
64 SAT models replayed by both oracles. The first, overly strict harness
required both oracles to decide the original input and failed on 13 cvc5
5-second timeouts. R111 uses the established affine policy: at least one
independent original verdict, plus both model replays for SAT. Those oracle
limits remain recorded; neither native code nor input answers changed.

Evidence identities and reproduction:

- Native source: `source-r109.tar.json`, SHA-256
  `9d526bb3ef649e2732436ff5792e8a4e4a0c27a848399fcbfb07a6ee33a7d64a`;
  CLI: `core-r109/xolver`, SHA-256
  `15058bb39aadf06f7cb0a992b395376c03a9adb19798d6714934908762b91fe9`.
- Full acceptance: `acceptance-r110/` and `acceptance-r111/intervals/`;
  tooling-only qualification: R112. Later overlays retain the R109 native
  file hashes and frozen executables.
- ExperimentOS experiment `xolver-arithmetic-fixed160-r109-20261026`;
  its `fixed160-r109.yaml` invokes `tools/remote/compare_arithmetic_case.py`.
  Reproduce scoring with
  `python3 tools/remote/summarize_arithmetic_comparison.py --runs validation/arithmetic-r103/fixed160-r109 --output validation/arithmetic-r103/recomputed-summary.json`.

Sixteen initial scheduler launches lacked CPU leases and were rejected before
any solver invocation. Leased retries produced all 160 reports. Nine database
statuses retained old failures after rerun, while their final exit files and
metrics were successful; R112 checks the actual lease, exit and report evidence.
Do not overwrite reports or edit the scheduler database to hide those attempts.

The historical gap inventory contains 56 cases: LIA 15, LRA 11, NIA 18,
NRA 12. Sampled next candidates include LIA simplex pivots (22, 92), LRA
propagation (48), LRA pivots (63), eager bit-vector search (27), and NRA root
merging/refinement (157). Other mechanism labels remain unprofiled. A sparse
proportional-bound implication experiment added no solves on 16 representative
gaps and was removed (`perf/ordered-threshold-chains`, `bcc757ec`). Do not
confuse that negative experiment with the retained interval implementation.
QCP checks here are pure-condition regressions; whole-program C verification
and the independent protected sets remain outstanding.

## Shared sparse simplex stage (R113–R119)

The accepted native snapshot is R114, based on the preceding delivered code;
the R117 alternative was rejected. The
[stage record](ARITHMETIC_SPARSE_SIMPLEX_STAGE_20261026.json) contains binary and
source hashes, all 160 report digests, detailed results and the rejected
experiment. Its evidence root is again `validation/arithmetic-r103/`.

Diagnostic samples put 27/49 frames for LIA index 22 and 33/49 for LRA index
63 in simplex pivots. The old entering rule preferred the largest absolute
coefficient without considering the number of affected rows. On index 63,
148/230 sampled pivot choices had a sparser eligible column; immediate coefficient
update estimates were 22,887,792 versus 13,294,541. These are local estimates,
not a prediction of an unchanged search trajectory.

`GeneralSimplex` now shares one entering-variable implementation for both
inequality directions, preferring fewer incident rows before coefficient
magnitude and variable index. Eligibility and Bland fallback are unchanged.
This applies to clients of the shared simplex, including LRA and LIA; it adds
no per-input rule or feature gate and retains their distinct backtracking
policies. Existing diagnostic configuration can record sparse elimination work.

The fresh R114 comparison uses R109, R114 and the same frozen Z3, with the
60-second / single leased physical CPU / 16 GiB protocol above:

| Version | Raw decisions | Verified decisions | Unknown | Timeout | Verified PAR-2 total (s) |
| --- | ---: | ---: | ---: | ---: | ---: |
| Xolver R109 | 79 | 76 | 3 | 78 | 10317.216 |
| Xolver R114 | 81 | 78 | 3 | 76 | 10117.226 |
| Z3, fresh round | 125 | 109 | 0 | 35 | 6342.174 |

Three SAT gains passed independent model replay, with one SAT loss:

| Primary index / member suffix | R109 (s) | R114 (s) |
| --- | ---: | ---: |
| 11 / `QF_LIA/slacks/30-28.slack.smt2` | timeout | SAT 13.276 |
| 63 / `QF_LRA/latendresse/ecoliFBAyicesTest-3875-4.smt2` | timeout | SAT 10.355 |
| 92 / `QF_LIA/slacks/20-24.slack.smt2` | timeout | SAT 0.598 |
| 6 / `QF_LIA/dillig/40-12.smt2` | SAT 0.425 | timeout |

No opposite verdict, process error, memory-limit result or invalid model replay
was observed in this round. The net gain is two verified decisions and about
200 seconds of PAR-2; index 6 is a real unresolved performance regression.
These results do not establish superiority to Z3. Independent confirmation
boundaries for indices 75, 115 and 148 remain unchanged.

Server acceptance R115 passed all 36 tasks: 1,656 unit tests / 794,902 assertions,
892 regressions, architecture/harness checks, differential/model checks and
the explicit known-gap contracts. The CLI is `core-r114/xolver`, SHA-256
`94fb80751bfca3de8f13838792109f2b8cca14e6c45cecdfdb506da5a179b82d`.
Its native source manifest is `source-r114.tar.json`, SHA-256
`58742e06440b4955ebf975f1337c918622c518958c24cfa2f3e6ea913bb62c35`.
The later source qualification restores exactly those native file hashes;
documentation updates do not require rebuilding an identical native snapshot.

The bounded-repair-first R117 alternative did not recover index 6. It failed
the known-gap 20-second check and a UFNIA 240-second regression, while a Z3
model query in the linear differential suite also timed out at 5 seconds.
Its full round returned 70/71/120 raw decisions and 67/68/105 verified decisions
for R109/R117/Z3, with substantial host/timing variation: unchanged R109 index
101 moved from 7–8 seconds in earlier rounds to a timeout. Its apparent recovery
by R117 is not evidence of a new capability. Preserve the negative result on
`perf/simplex-feasible-repair`, `cab35356`, and do not merge that policy.

QCP's existing development corpus has 313 exported queries; R115 decided all
of them consistently with Z3. This leaves no coverage gap on that limited
pure-condition corpus. A full pinned QCP source export and isolated Coq 8.20.1 /
Dune 3.17.2 toolchain are present under `dependencies/qcp-08cc7a0f` and
`dependencies/qcp-tools`. Initial controller run
`branch_destruct-20261026224840` closed with a CPU-lease infrastructure blocker
before symexec; its record remains `qcp-jobs/branch-blocked-finalization.json`.
The fresh run `branch_destruct-20261026235539` subsequently completed the
controller's native compilation routes and final-check for one C input with
ten VCs, with C and specification byte-identical. It reused 143 base proof
artifacts and compiled all four current source files. **Trust-audit correction:**
the generated auto module contains ten `Proof. Admitted.` placeholders. This
qualifies infrastructure only: **zero independently verified programs**. It is
not an Xolver/Z3 backend comparison. Internal SMT calls were not
instrumented; no external comparison invocation of either solver was made.
Do not count the 313 extracted queries as verified programs. Exact source,
proof, timing and controller evidence is indexed in the next stage record.

## Integer refinement and model validation (R132/R133, 2026-10-27)

Evidence: [stage record](ARITHMETIC_INTEGER_EFFORT_STAGE_20261027.json).
Delivery PR: [#45](https://github.com/fuqi-jia/Xolver/pull/45).
Merged main: `37c71d78585465a7389255c23d3269a2c043d88a`;
[main CI 40377408280](https://github.com/fuqi-jia/Xolver/actions/runs/40377408280)
passed both jobs.

Standard LIA checks previously registered branch and normalization atoms even
though the SAT callback discards their branch lemmas. Those observed variables
could extend the next partial assignment before Full-effort integer repair ran.
The component reproduction expanded two input atoms to five and failed 40
assertions. The relevant integer-core files match the preceding main revision.

`LiaSolver` and the shared `IntegerReasoner` now pass check effort explicitly:
Standard retains conflicts; Full performs vocabulary-extending refinement and
validated model repair. The one-argument integer-reasoner API still defaults to
Full. LRA and LIA backtracking policies and public Solver semantics are unchanged.
The general rule is that a branch lemma which will not be installed must not
first extend the observed SAT vocabulary; sound installed entailments remain
available during propagation.

R133 passes **1,659 unit tests / 794,992 assertions**, including primitive
coupled rows and the explicitly pinned rational-bound countermodel. The old
countermodel test's request for a Standard branch lemma was replaced by these
stronger model/witness checks. All 35 remaining R134 acceptance tasks pass,
including 892 regressions, independent model checks and the QCP regressions.
The CLI is `core-r132/xolver`, SHA-256
`084f469bc0a58f45040923b9388037f046153a1bb5f788817067dad1437fbcac`.
`source-r133.tar.json` has SHA-256
`5fdcb136503cb10a2f3857c32a57b610d0912684e7a395acd553b8dfc4942733`;
its native code is identical to the R132 build, with only test changes.

Fresh formal comparison, 160 inputs, 60 seconds / one physical CPU / 16 GiB:

| Version | Raw decisions | Independently verified | Verified PAR-2 |
| --- | ---: | ---: | ---: |
| Frozen preceding main R114 | 74 | 71 | 10878.492 |
| Candidate R132 | 75 | 72 | 10739.232 |
| Same-round frozen Z3 | 122 | 107 | 6781.590 |

Both Xolver versions returned two unknowns; timeouts changed from 84 to 83.
There were no opposite verdicts, solver errors, memory-limit outcomes or invalid
exported models. The net gain is one verified decision and 139.259 seconds of
verified PAR-2. Gains are indices **6, 7, 11, 59**; losses are **45, 52, 100**.
Every loss remains in the report. Index 6 recovers the known sparse-pivot-era
regression: timeout to SAT in **2.509 seconds** formally, and **0.297 seconds**
in the targeted comparison; both exported models pass independent replay.
Pure LRA code is unchanged, so the opposing changes at 52/59 reflect timing or
search variation, not added theory coverage. Other gains also include cases
solved by earlier versions in other rounds. Do not compare historical aggregate
scores as if host conditions were constant.

The 196 successful leased runs use 42 distinct physical cores with no overlap
or discrepancy between leased and actual comparison CPUs. Six original jobs
without CPU leases stopped before solver execution; a separate leased retry
completed those exact inputs without overwriting valid reports. Earlier R123
acceptance entries `architecture` and `known-gaps` lacked leases and are excluded;
the rejected ordering experiment was not merged. Other closed prototypes and
their evidence are retained in the stage record. The propagation memory-pool
experiment was not repeated.

This does **not** exceed Z3, and confirmation limits for 75/115/148 remain
explicit. Neither protected set was read or run. Require PR CI and main CI on
the merge commit for delivery; an extra server checkpoint is not required.

## Shared remainder lattice cuts (R140/R141, 2026-10-27)

Evidence: [stage record](ARITHMETIC_REMAINDER_LATTICE_STAGE_20261027.json).
Delivery PR: [#46](https://github.com/fuqi-jia/Xolver/pull/46).
The preceding main is `37c71d78`; its frozen CLI is R132.

Independent quotient/remainder encodings hid a useful lattice fact from LIA.
For one dividend and positive magnitudes `m | n`, `r_n-r_m` is a nonnegative
multiple of `m`, at most `n-m`. `IntDivModLowerer` now emits the first gap as
`r_n = r_m OR r_n >= r_m+m`, plus the upper bound. Each remainder connects to
its nearest available multiple, keeping generated syntax linear in the number
of divisions. This adds no integer variables or feature gates. Zero divisors
are excluded; negative divisors use their absolute magnitude. Different
dividends and assertion scopes remain independent. Existing Solver semantics
and the distinct LRA/LIA backtracking policies are unchanged.

Primary index 26, `soft_float_3a.c.cil.c_4.smt2`, changes from timeout to
independently confirmed UNSAT in **0.0466 seconds** formally and **0.0458
seconds** in the targeted round. In a separate diagnostic run, the old version
made 2,043 pipeline calls and 2,732 pivots before its 20-second external cap;
the candidate used 31 Standard checks, ten Full checks and one pivot. Generated
assertions change from 23 to 35. These diagnostic timings do not replace the
formal paired measurements.

R141 passes **1,662 unit tests / 797,155 assertions**, including exact signed
witnesses, arbitrary-precision constants, incomparable moduli and scope pop.
All **36** R142 acceptance tasks pass, including **897 regressions**. Two new
SAT fixtures pass both Z3 and cvc5 model replay. All three new UNSAT fixtures
are independently confirmed by Z3; cvc5 confirms the two LIA fixtures and
times out at 60 seconds on the nonlinear fixture. Its unresolved result is
retained, not treated as an additional confirmation.

Fresh 160-case comparison, 60 seconds / one physical CPU / 16 GiB:

| Version | Raw decisions | Independently verified | Verified PAR-2 |
| --- | ---: | ---: | ---: |
| Frozen preceding main R132 | 75 | 72 | 10916.801 |
| Candidate R140 | 78 | 75 | 10604.840 |
| Same-round frozen Z3 | 121 | 106 | 6942.345 |

Gains are **7, 26, 64**; there are no lost verified results, opposite verdicts,
solver errors, memory-limit outcomes or invalid exported models. The net gain
is three verified decisions and 311.961 seconds of verified PAR-2. Only 26 is
a reproduced new algorithmic solve. The unaffected paths at 7 (near budget)
and 64 (pure NRA) changed search/timing outcomes; do not attribute new theory
coverage to those changes. Candidate unknowns change from three to two.
Unconfirmed 75/115/148 remain excluded.

The CLI is `core-r140/xolver`, SHA-256
`747ce2fe4ae6b9c4276f366189063730988a8fd6c2981249f3af95bf3cef0a9a`.
The tested source manifest is `source-r141.tar.json`, SHA-256
`da8a7971eb51f53c4803f8b299ba14d8cd74b885294a92554f545c8ce2cb676c`.
Its native code is identical to R140, with added tests. The 197 delivery runs
use 42 distinct physical cores, with no overlapping leases; all 160 actual
comparison CPUs match their leases. `H_actual` affinity is sampled before
`taskset`, so the audit also checks every generated launch script. One targeted
job without a lease stopped before execution and was retried with a lease.

Closed prototypes: shared polynomial bulk projection R137 verified 5/15 with
both versions, with only 0.276 seconds of PAR-2 change; the R139 auxiliary
integer representation verified 4/12 with both versions and solved no new
case. Neither is selected. The memory-pool experiment was not repeated.

The existing 313 QCP conditions still agree across CLI, SV and Z3 (291 UNSAT,
22 SAT). The SV executable remains byte-identical to preceding main; this is
not an end-to-end program-backend improvement. The prior pinned QCP proof
qualification is infrastructure only; all ten auto VCs are admitted and the
verified-program count is zero. The public pinned CLI exposes no SMT replacement
option. Implement an explicit backend discharge interface rather than waiting
for a source location, and reconstruct every VC, including auto placeholders. Both protected evaluations remain unused. This stage does
not exceed Z3; require final-head PR CI and merge-commit main CI for delivery,
without another server checkpoint.

## Conditional affine lattices (R144/R146, 2026-10-27)

Evidence: [stage record](ARITHMETIC_AFFINE_LATTICE_STAGE_20261027.json).
Delivery PR: [#47](https://github.com/fuqi-jia/Xolver/pull/47).
Merged main: `45a69aaa7242b95f8d4d6a497567c580cf573de4`; both jobs in
[main CI 40401271301](https://github.com/fuqi-jia/Xolver/actions/runs/40401271301)
passed.
Preceding [#46](https://github.com/fuqi-jia/Xolver/pull/46) merged as
`db327e7e021d551a22745308834326e65edf0942`; both jobs in
[main CI 40389912116](https://github.com/fuqi-jia/Xolver/actions/runs/40389912116)
passed.

`LiaSolver::handleDisequalities` previously split using only the gcd of raw
coefficients. In ring case 22 this is 1, while either active equality branch
implies a step of 512. The shared, stateless `IntegerAffineProjection` uses
budgeted sparse integral unit pivots to derive `offset + step*Z`. Splits cite
all used equality literals, including theory-combination equalities; fixed
forms and impossible residues keep their exact meanings. Unsupported/exhausted
projections retain the old lattice. LRA/LIA backtracking policies are unchanged.

Frozen CLI R144 SHA-256:
`c1604d8bb498cfafedfdb0d2e8f422fcd0d6fb1d138518963d3621b7a870e662`.
R146 adds only correctness tests; its CLI and SV hashes match R144. Native
qualification passed **1,667 tests / 798,457 assertions**. All **37 acceptance
tasks / 901 regressions** passed. Four new regressions cover conditional
branches, nonzero cosets and projected constants; independent Z3/cvc5 decisions
and exported SAT-model replay passed. Scope tests repeat UNSAT → pop → SAT
three times. All 220 audited build/target/formal/acceptance/recheck runs held
single-physical-core leases across 42 physical cores, with no overlaps.

Fresh 160-case comparison (60 seconds / one core / 16 GiB per invocation):

| Version | Raw decided | Verified decided | Verified PAR-2 |
| --- | ---: | ---: | ---: |
| Frozen R140 baseline | 75 | 72 | 10841.770 |
| Frozen R144 candidate | 78 | 75 | 10461.618 |
| Same-round Z3 | 120 | 110 | 6469.944 |

No wrong verdicts, invalid exported models, solver errors or memory failures.
The three independently confirmed ring gains are 22, 85 and 95: formal times
0.220, 0.534 and 28.766 seconds; targeted times 0.220, 0.535 and 5.428 seconds.
Preserve the formal SAT gain 45 and LRA loss 59 in the score. Each was rechecked
three times with both frozen versions: both versions returned checked SAT in
every repetition (about 3.2–3.6 seconds). Neither change establishes another
algorithmic gain or a reproducible LRA regression. Do not replace formal rows
with the diagnostic repetitions. Net verified gain is three; PAR-2 improves
380.152 seconds. Candidate still trails Z3 substantially. Unverified Xolver
75/115/148 remain excluded; neither protected set has been evaluated.

QCP correction is part of this effective code delivery: the earlier
`branch_destruct` controller success is **zero verified programs**, because its
auto file admits all ten VCs. Current `gcd` auto output similarly admits six
VCs. A selectable VC-discharge prototype now runs outside the solver in a
separate branch, but pure UNSAT candidates are not full proofs. Full comparison
requires independently reconstructed original VCs, audited proof assumptions
and complete program checks for each frozen backend. Do not count opaque QCP
internal calls as external comparison queries or assume they are zero.

## Audited QCP backend qualification (R150, 2026-10-27)

Evidence: [backend stage record](QCP_BACKEND_QUALIFICATION_STAGE_20261027.json).
Delivery: [PR #48](https://github.com/fuqi-jia/Xolver/pull/48), merged as
`741b447c40d7a5384dc405c719d6c0c97516369e`; both jobs in
[main CI 40415965574](https://github.com/fuqi-jia/Xolver/actions/runs/40415965574) passed.
Implementation branch: `feat/qcp-vc-backend`; native source manifest
`source-r150.tar.json`. That qualification used frozen R144 and native
production source matching qualified R146. Python integration changes passed
**21 protocol tests**, architecture checks and three real program-record audits.
Both protected evaluations remain unused.

The pinned public QCP CLI exposes no backend-selection option. The implemented
interface runs after VC generation: `prepare_qcp_controller.py` freezes a separate
controller copy that promotes every admitted auto witness into manual proof
obligations during both generation and final replay. The pinned native QCP
checkout, C body and specification stay byte-identical. Its internal SMT remains
a common opaque frontend component; its query count is unknown.

`qcp_backend.py` dispatches assigned typed arithmetic refutations to either
frozen Xolver or Z3 under one leased physical CPU, 60 seconds and 16 GiB per
query. Every UNSAT result prepares a proof candidate. The identical common
`LLM_pre_process ltac:(first [lia | nia])` bodies passed every original whole VC
unchanged with both backends. Canonical group acceptance, parent checking,
final publication and independent final-check all passed. The final auto and
manual modules contain zero `Admitted`; each manual contains ten `Qed` witnesses.

| Backend | Verified C programs | Whole VCs | Actual external SMT queries |
| --- | ---: | ---: | ---: |
| Frozen Xolver R144 | 1 | 10 | 14 |
| Frozen Z3 5.3.2 | 1 | 10 | 14 |

These are two qualifications of **one unique development program**,
`branch_destruct.c`, with identical source and goal hashes. All 45 selected
native workflow runs held single-physical-core leases without overlap. This
interactive qualification is not a fresh automated same-budget program-suite
performance comparison; queue/owner elapsed and repeated proof-stage compilation
must not be treated as such a result. Neither an end-to-end speed lead nor
superior program coverage has been established.

`audit_qcp_program.py` checks the exact named VC interface, completed witnesses,
absence of admitted case assumptions, matching canonical state/final-check and
frozen backend candidates. It checks coverage against the supplied canonical native records; provenance
is authenticated separately by the stage's EOS audit. Missing backend reports keep query
counts unknown. Real negative checks reject the old ten-admission tutorial
record and the GCD record that still admits six auto VCs, even though their
controllers reached `done`. GCD's three manually proved top-level VCs and its
two auxiliary SMT calls remain component evidence, with zero verified programs.

Closed arithmetic prototype R149 preferred stronger all-integer GMI cuts, with
the existing size/count budgets and a pure-cut fallback. It passed **1,668 unit
tests / 798,791 assertions**, but the 15-case paired check verified 11 with each
version, gained nothing and worsened PAR-2 by 4.394 seconds. Keep it unmerged on
`perf/strong-integer-cuts` (`e4d50968`); no full160 rerun is justified for that
idea. Source R150 restores the delivered native source and retains frozen R144.

The remaining performance objectives still require further general solver
improvements and a frozen automated program-suite comparison. Preserve the
existing Git/CI/source/frozen-hash evidence route; an extra server archive is
not a delivery prerequisite.

## Integer choice lattices and shared contexts (R174, 2026-10-27)

Evidence: [qualified stage record](ARITHMETIC_INTEGER_CHOICE_CONTEXT_STAGE_20261027.json).
Code revision: `48f6964124872a75e4fc42d7276a0cf2d1559366`, delivered by
[PR49](https://github.com/fuqi-jia/Xolver/pull/49) as main
`e6e1c595db2480bcc106177c0cdb4e2fa20836ae`.
[Final-head PR CI](https://github.com/fuqi-jia/Xolver/actions/runs/40428978372)
and [main CI](https://github.com/fuqi-jia/Xolver/actions/runs/40430617621)
both passed `build-test` and `proof-gate`. Native source manifest is
`source-r174.tar.json`; the server
export may advance after this qualification without invalidating its hashes.

`IteLowerer` previously replaced each arithmetic choice with an unrelated
integer. Branches sharing an affine part and a residual gcd now retain
`common + gcd * freshInt`, with both exact guarded definitions. Int-valued
nonlinear terms, UF applications and array reads remain opaque arithmetic atoms.
The transformation applies by value sort across theories. Real choices keep
their established lowering after an unsuccessful broader experiment.

`LiaSolver::handleDisequalities` now excludes nonzero LP values inside an
unreachable integer lattice gap, with positive denominator scaling and every
used equality premise retained. The continuous zero-only handler is unchanged.
A shared `IntegerAffineContext` prepares the current equality snapshot once per
Full check and indexes variable dependencies. Projections visit the transitive
relevant component in source order. The compatibility helper remains available;
no prepared context survives into another check or scope. LRA/LIA assignment
policies, APIs, cut budgets and runtime-oracle policy are unchanged.

Ring case 0 exposes the root cause: the lowered disequality changes from 30
terms with coefficient gcd 1 to 28 terms with gcd 64. Its formal runtime changes
from a 60-second timeout to **0.186 seconds**, independently confirmed by Z3.
A diagnostic records **107 LIA checks** (23 Full, 84 Standard), compared with
thousands before the baseline timeout. Separate tests prepare 1,001 equalities
once, then complete each relevant projection within a budget of 128, preserving
indirect dependencies and fresh-context explanations.

Frozen CLI SHA-256:
`90d6e0027bdacdcad065845c92f0e9d1efac3390c6a65809d379958643733936`.
The SV executable retains SHA-256
`99130012b880f255cd8bbaf456d4031d07649792c83c430acb5649a547bb89ef`.
Native qualification passed **1,674 tests / 801,135 assertions**, the targeted
**37 tests / 4,430 assertions**, and all **37 acceptance tasks / 909 regressions**.
Eight fixtures have independent decisions and SAT-model replay. All 219 audited
runs used single-physical-core leases across 65 cores without overlap; every
formal invocation matched its assigned CPU.

Fresh fixed160 comparison: each invocation receives 60 seconds, one physical
core and 16 GiB; both frozen Xolver versions and Z3 rotate on the same CPU.

| Version | Raw decided | Verified decided | Verified PAR-2 |
| --- | ---: | ---: | ---: |
| Frozen preceding main R144 | 82 | 81 | 9673.930 |
| Candidate R174 | 85 | 84 | 9360.687 |
| Same-round frozen Z3 | 121 | 113 | 5900.908 |

Verified gains are **0, 91 and 100**, with no lost results. Their formal times
are 0.186, 3.195 and 6.192 seconds; targeted times are 0.171, 3.166 and 6.229.
Each preceding-main invocation timed out in both comparisons. PAR-2 improves
**313.243 seconds**. Both Xolver versions return two unknowns; no wrong verdict,
invalid exported model, solver error or memory failure was observed. Individual
matched cases can still slow down; all original observations remain recorded.
This does not exceed Z3 or the user's 125/160 reference target.

The shared replay tool now expands `root-of-with-interval` only after an exact
rational Sturm count proves unique isolation. Fresh Real witnesses retain the
polynomial, interval, original model expressions and all original assertions.
The replay language permits witness polynomials. Six roots in SAT cases **75
and 148** passed independent Z3 replay; 16 protocol tests and two negative
controls (both rejected by Z3 and cvc5) cover the checker. The first cvc5 replay
of case75 timed out at60s; that boundary is retained. These model confirmations
apply to both versions and are separate from the three algorithmic gains.
Historical tables excluding75/148 remain historical; **UNSAT115 is still
unconfirmed and excluded**. Unsupported model values stay unverified.

R153 lost verified coverage; R155 tied coverage with worse PAR-2. R162 tied
coverage with a small PAR-2 improvement but retained regressions from repeated
projection preparation. The R170 unit-gap deferral experiment lost coverage in
its 15-case check and was reverted without a full160 rerun. Their raw records
remain in the stage artifact. The selected R174 implementation passed the full
closure above. No propagation-pool experiment was reopened.

QCP component regressions passed with the new CLI; the independently checked
whole-program qualification remains the one unique development C program in
PR48. A fresh frozen program-suite performance comparison is still required.
Neither protected set has been evaluated. Continue from Git, successful CI,
source manifests and frozen hashes; an extra server archive is not a delivery
gate after GitHub CI is green.

## Affine algebraic model replay (R184, 2026-10-27)

Evidence: [qualified stage record](ARITHMETIC_ALGEBRAIC_MODEL_STAGE_20261027.json).
Code revision `1be82585fe84e3d6b3db0f35ad29e7e537030037`, review branch
`perf/algebraic-definition-replay`, builds on delivered main `e6e1c595`.
Use the final-head PR and merged-main checks as the delivery record. Native
source is `source-r184.tar.json`; `git-code-r184.json` checks its 124
non-documentation overlay files against the code commit. Documentation-only
changes do not imply another native executable.

NRA/NIRA previously skipped unconditional definition elimination because
`ModelConverter` replayed rational values only. The shared converter now replays
affine algebraic definitions through exact `RealValue` operations. Typed model
values take precedence, algebraic results clear old rational defaults, and
integer targets require exact integer values. Unsupported expressions and
missing constrained dependencies still fail reconstruction.

Elimination can also remove a definition's last free parameter from the
residual formula. `SolveEqs::commit` records these parameters only after a full
residual occurrence scan, before replacing assertions. The converter supplies
zero only when neither model channel provides a value; supplied parameter
values and the strict standalone reconstruction contract remain intact. The
existing base-scope and difference-logic policies, public Solver API and tested
LRA/LIA assignment policies remain unchanged. There is no new feature gate or
runtime external oracle.

Primary case **152**, an inductiveness query with two linear next-state
definitions, now exports a complete SAT model for the original assertions.
The instrumented snapshots show four active symbols becoming two, two
definitions eliminated with 143 substitution-work units, and a DAG change
50→46. Baseline local search spends 265.9 ms before CAC (2098.3 ms) and CDCAC (402.3 ms)
return unknown; the candidate finds a model in one 3.4 ms local-search call and
does not enter either covering engine. These diagnostic timings are excluded
from scoring. The earlier transformed-input diagnostic is causal evidence,
not an additional solved input.

Frozen CLI SHA-256:
`c59cea2ce49f62f793fe9de28527da32ab2d4af2456347f0753384ff39433ff9`.
The SV executable retains SHA-256
`99130012b880f255cd8bbaf456d4031d07649792c83c430acb5649a547bb89ef`.
Native qualification passed **1,678 tests / 801,163 assertions**, including
**35 targeted tests / 135 assertions**. All **38 acceptance tasks / 913
regressions** passed, together with 1,018 native-theory differential cases and
703 exported models checked by both independent engines. Four new regressions
and original 152 have separate decision/model evidence. Two algebraic fixture
replays are unresolved in cvc5 but SAT in Z3; free-parameter and original 152
models replay SAT in both. No budget was extended.

Fresh fixed160: each frozen version receives 60 seconds, one physical core and
16 GiB, with solver order rotated on the same CPU.

| Version | Raw decided | Verified decided | Verified PAR-2 |
| --- | ---: | ---: | ---: |
| Preceding main, frozen R174 | 88 | 87 | 9056.937 |
| Candidate R184 | 89 | 88 | 8944.209 |
| Same-round frozen Z3 | 124 | 116 | 5505.803 |

The sole verified gain is **152**, with no lost result. It takes 0.1696 s in the
formal round and 0.1687 s in the 32-case NRA check; the baseline returns unknown
in both. PAR-2 improves 112.729 seconds. Baseline has two unknowns and 70
timeouts; candidate has zero unknowns and 71 timeouts. Unknown 79 becomes a
timeout and is not a new solve. No wrong verdict, invalid exported model,
solver error or memory failure was observed. **UNSAT115 remains unconfirmed
and excluded**.

The same R174 binary scored 84 in the preceding frozen round and 87 here. That
cross-round difference reflects search/timing variation; only this round's
**87→88** belongs to the new code. Xolver still trails Z3; the reference target
remains at least 126/160, above the historical Z3's 125/160.

The native source/binary/lease audit passed as EOS `e305dee38dd8`: 235 runs on 65
physical cores, no overlapping leases, and every formal invocation matched its
assigned CPU. The first audit task received an empty CPU lease and was rejected
before execution; only the audit was retried. Full comparison is EOS
`4e96d995ab00`; acceptance is `937f368d8700`; targeted NRA is `5a918215e634`;
original-model checks are `d7043c716ec6`.

QCP component regressions passed. The whole-program qualification remains the
previous one unique development C program in PR48; this stage makes no new
whole-program performance claim. Neither protected set has been evaluated.
Continue using Git, successful GitHub CI, source manifests, frozen hashes and
these acceptance records. An additional server archive is not a delivery gate.

## Delivery receipt and typed QCP storage ranges (2026-10-27)

The R184 arithmetic stage was merged in
[PR50](https://github.com/fuqi-jia/Xolver/pull/50), producing main
`7a7e40a7f5ea54df920baa2634a669717fa0a545`. Both jobs passed in
[PR CI](https://github.com/fuqi-jia/Xolver/actions/runs/40437207152) and
[main CI](https://github.com/fuqi-jia/Xolver/actions/runs/40439231930).
R184 remains the selected arithmetic binary. Later experimental binaries below
do not replace its qualification.

The [typed-range stage record](QCP_TYPED_RANGE_STAGE_20261027.json) records a
QCP adapter improvement: supported positive assertions owning signed `Int`
cells contribute the exact storage range supplied by `store_int_range`.
Unknown heap syntax, negative contexts and disjunctions contribute no range
facts. Unowned `Z` variables remain unbounded. Exported assumptions and both
adapter source hashes are recorded with each query.

The adapter reconstructs complete original Rocq statements, deriving ranges
with the public storage lemma. Pure-only conclusions avoid spatial splitting;
spatial cancellation must finish its branch. Twenty-five native integration
tests passed in EOS `b3b49552a328`. Four newly generated R222 safety candidates
passed unchanged in EOS `b5de49ca4ab5`; other obligations still require checked
public remainder/gcd arithmetic. No SMT result becomes a proof assumption.

Both frozen backends completed canonical GCD final-checks with identical C,
specifications and frontend: Xolver EOS `145b082b14fb`, Z3 `dac58200d7cc`.
The independent coverage audit finds **one program and nine whole VCs per
backend**, zero admitted auto witnesses. Each R210 discharge uses twelve
external queries, all UNSAT; two formerly SAT weaker projections are now UNSAT
with justified type ranges. Repeated R222 attempts do not add query or program
coverage. Total unique qualified development C programs, including the earlier
branch example, is **two**. Internal symbolic-executor query counts remain
unknown. Reconstruction attempts differ, so these timings establish no fair
end-to-end speed advantage or superiority over Z3.

Boundary candidates and integer scaling are separate experimental methods.
The common boundary framework takes theory-supplied admissible endpoints and
requires complete candidate validation. Integer primitive-ray scaling has its
own arithmetic-specific checks. Shared linear coordinates exposed a growing
integer branch ray; a reproduced stale decision-vocabulary cache was fixed,
but that fix alone did not recover all lost solves. R208, R219, R224 and R227
remain unselected: their formal comparisons had no added verified solve and
lost results. These experiments establish no selected boundary-search gain.
Neither protected set has been evaluated, and an extra server archive is not a gate.

## Rational polynomial real definitions (2026-10-27, R258/R260)

The preceding typed QCP range stage merged as
[PR51](https://github.com/fuqi-jia/Xolver/pull/51), main
`3091a4cc7c75c1fe60a9be57d6a919723953a6ad`. Both jobs passed in
[PR CI](https://github.com/fuqi-jia/Xolver/actions/runs/40474461100) and
[main CI](https://github.com/fuqi-jia/Xolver/actions/runs/40478407991).

The [polynomial-definition stage record](ARITHMETIC_POLYNOMIAL_DEFINITIONS_STAGE_20261027.json)
qualifies implementation `3fd4939ad110e5334f8a7b0a449d1685bb50af0b` against that
main. `checkSatGround -> SolveEqs -> ModelConverter` now removes unconditional
real polynomial definitions even when the defined variable has nonlinear uses,
then reconstructs their exact algebraic values. Rational replay remains the
fast path. Real division by a nonzero numeric literal is an admissible rational
coefficient; variable/zero divisors and integer division retain their previous
handling. Missing dependencies, unsupported algebraic operations or exhausted
replay resources cannot manufacture a model. Integer elimination, shared
UF/array guards, base-scope restrictions and LRA/LIA root policies remain.

Original **79**, `QF_NRA/20200911-Pine/1599121904575726000.smt2`, previously
retained one polynomial alias and timed out in covering/root isolation. The
candidate eliminates both aliases: four variables become two, DAG nodes
57→53, substitution work 156. The early R256 prototype rejected `u^3/6` and
`u^5/120`, eliminated only one alias and gained nothing; R258 completes this
case without a filename rule. The transformed-query diagnostic and instrumented
timings are excluded from scoring. The candidate model for the complete
original input replays SAT in both Z3 and cvc5.

Frozen CLI SHA-256:
`65ec6a15c7d4c61506689a6bbed023aaef8f95ac2e1e9738fc082ad7f687c33d`.
The SV binary retains `99130012b880f255cd8bbaf456d4031d07649792c83c430acb5649a547bb89ef`.
Panda1 qualification passed **1,684 unit tests / 801,216 assertions**, including
**67 targeted tests / 12,680 assertions**. All **38 acceptance tasks / 915
regressions**, 1,018 native-theory differential cases and 703 model checks passed.
Eight separate original-input/fixture checks are confirmed. Three small
algebraic fixture replays remain unresolved in cvc5 but pass Z3; original 79
and retained gain 152 pass both. No budget was extended.

Fresh fixed160, 60 seconds / one physical core / 16 GiB per frozen version,
with order rotated on the same assigned CPU:

| Version | Raw decided | Verified decided | Verified PAR-2 |
| --- | ---: | ---: | ---: |
| Preceding main, frozen R184 | 89 | 88 | 8956.654 |
| Candidate R258 | 90 | 89 | 8841.332 |
| Same-round frozen Z3 | 124 | 115 | 5609.728 |

The sole verified gain is **79**, SAT in **0.1359 s** against a baseline
timeout; same-round Z3 takes 4.6061 s. There are no lost verified results,
opposite verdicts, invalid exported models, process errors or memory failures.
PAR-2 improves 115.322 seconds. Baseline/candidate have 71/70 timeouts and
zero unknowns. **UNSAT115 remains unconfirmed and excluded**. The 32-case NRA
check independently records 17→18 verified results, only gain 79, no losses.
Xolver remains below Z3; this stage establishes no overall superiority.

Build EOS `9bd8a9ffb90d`; NRA `6af467375fca`; full comparison `2230ce9bbfde`;
acceptance `3fe419f85864`; original-model checks `cf2b449ac3c6`;
profile `ac0fb00ceb1a`; source/binary/CPU audit `d5a4bead935e`.
The audit matches all 233 stage runs to physical CPU leases on 65 cores,
with no overlaps and exact formal process affinity. Source manifests and Git
inventory identify the frozen binaries. QCP component regressions pass; the
two previously qualified unique development C programs gain no new whole-program
coverage or end-to-end performance claim here. Neither protected set was used.

R231, R234, R238, R242, R248 and R253 remain unselected, as detailed in the
stage record. Reproduced model-phase and registry-wiring defects did not yield
verified solve gains on their tested sets. Their fixes are not asserted to
explain or recover the shared-coordinate performance regression. Boundary
search remains independent of integer scaling; neither experimental bundle
is included in this candidate. The earlier 96-case subset actually contains
48 LIA + 16 NIA + 32 LRA inputs; its historical “all-linear” label was wrong.
The fixed160 manifest contains 48 LIA, 48 NIA, 32 LRA and 32 NRA inputs.
Input hashes and historical scores are unaffected by this label correction.

Continue from Git, CI, source manifests, frozen hashes and these acceptance
records. The cancelled `validation/current-main.json` archive is not a gap or
a delivery requirement.

## Partial boundary assignment and linear completion (R264/R266)

The preceding polynomial-definition stage merged in
[PR52](https://github.com/fuqi-jia/Xolver/pull/52), main
`be8e9cad1be90ba3e18e1d97004145a1f0ac93c8`. Both jobs passed in
[PR CI](https://github.com/fuqi-jia/Xolver/actions/runs/40499991484) and
[main CI](https://github.com/fuqi-jia/Xolver/actions/runs/40502199358).

The [partial-linear-model stage record](ARITHMETIC_PARTIAL_LINEAR_MODELS_STAGE_20261027.json)
qualifies implementation `f967dccbef51a5becee6200ab0edf13170b79f2e` against that
main. Merge `870cb5f1` connects the histories without changing the qualified
source/test bytes. The source/header census is 653, with no layer violation.

The root cause is incomplete candidate construction: a few variables occur
inside products, while many remaining coordinates form a coupled linear
system. Small whole-model guesses miss its large coordinates. A diagnostic
automatically selected three product variables in original **157**. Setting
them to 1 let the previous binary solve the strengthened query in 0.0425 s;
the resulting model satisfies the full original input in both Z3 and cvc5.
The 0/-1 strengthened queries are UNSAT, which proves nothing about original
UNSAT and is not scored as such.

`PartialLinearModelSearch` now selects a deterministic monomial cover, tries
admissible boundary/simple corners, solves each remaining linear system with
exact simplex and checks every original polynomial at the complete point.
The domain-independent `boundaryCandidates` helper tries a supplied upper
endpoint before the lower endpoint. Open real endpoints are excluded; integer
clients round endpoints exactly and reject fractional completed models. The
production adapter added here runs at Full candidate effort in pure NRA;
other domains are not claimed as newly enabled. No integer scaling is involved.

Each attempt owns a fresh simplex context and shares a 20 ms / 100,000-work-unit
allocation. `GeneralSimplex::checkUntil` can yield without corrupting its
tableau; ordinary `check()` and the verified LRA/LIA backtracking policies keep
their existing semantics. A failed candidate creates no conflict, pruning
clause or original UNSAT result. There is no new runtime control or oracle.

Frozen CLI SHA-256:
`e7a8214e33b022d8e6acafc33fed8d00636d1da66c33ffb070a2695ed4504e34`.
SV retains `99130012b880f255cd8bbaf456d4031d07649792c83c430acb5649a547bb89ef`.
Panda1 passed **1,689 unit tests / 801,249 assertions**, **98 targeted tests /
158,920 assertions**, all **38 acceptance tasks / 916 regressions**, and
1,018 native-theory differential cases / 703 models. Sixteen additional
coupled fixtures have independent Z3/cvc5 decisions, and all eight SAT models
replay in both. Four separate original/fixture checks also pass both engines,
including retained 79/152 and new 157. Gain 150 has an independently replayed
model in the formal comparison. These fixtures add no benchmark/program count.

Fresh fixed160 uses the unchanged manifest, frozen versions, rotated same-CPU
order and 60 seconds / one physical core / 16 GiB per solver:

| Version | Raw decided | Verified decided | Verified PAR-2 |
| --- | ---: | ---: | ---: |
| Preceding main, frozen R258 | 90 | 89 | 8824.108 |
| Candidate R264 | 92 | 91 | 8593.592 |
| Same-round frozen Z3 | 124 | 115 | 5609.677 |

Only **150** (`zankl/matrix-3-all-2.smt2`, SAT 0.6053 s) and **157** (the PRAY
geometric-offspring input, SAT 3.9705 s) are newly verified; there are no lost
results. Their same-round Z3 times are 0.0792/0.0424 s. PAR-2 improves 230.515 s.
Baseline has 70 timeouts / zero unknowns; candidate has 67 timeouts / one
unknown. The 77 timeout→unknown change is not a solved case. There are no
opposite verdicts, invalid exported models, process errors or memory failures.
**UNSAT115 remains unconfirmed and excluded**. The separate 32-case NRA round
records 18→20 verified results, exactly the same gains, no losses; PAR-2 changes
1689.860→1454.109. This remains below Z3 and is not a superiority claim.

Build EOS `69c98a222923`; NRA `9f838f5e7cb0`; full comparison `86b586e965ca`;
acceptance `eac97f59de82`; original models `96348ba107c0`; generated models
`824422727924`; profile `24bd23a036bf`; causal diagnostic `83701026ee61`;
source/binary/lease audit `4b4d875a9346`. The 252 audited runs match their
physical CPU leases on 65 cores, with no overlap or formal affinity mismatch.
Instrumented 157 spends 5.5 ms in completion but 3.64 s in two earlier box
checks; this remains an optimization opportunity, not an extra measured gain.
QCP component regressions pass; unique qualified development C coverage stays
two, without a new end-to-end claim. Neither protected set was used. The
cancelled server archive remains unnecessary.

The stage was merged through [PR #53](https://github.com/fuqi-jia/Xolver/pull/53)
as main `67fe12af35087fb0f57bf9696351ff6642fe13ee`. Both `build-test` and
`proof-gate` passed on the [PR CI](https://github.com/fuqi-jia/Xolver/actions/runs/40505591792)
and the [actual main CI](https://github.com/fuqi-jia/Xolver/actions/runs/40508939783).
These delivery checks do not introduce an additional server archive requirement.

### Rejected pending-inference scheduling experiment (R270–R275)

Profiles on primary NIA 24/37/113 showed 11/10/12 prepared linear inferences
still queued at CDCAC entry. R274 delivered these explained inferences earlier,
while retaining candidate-model commitments at their previous late stage.
The native failing reproduction is EOS `79f25a983699`; the repair passed
1,690 unit tests / 801,458 assertions, including 68 targeted tests / 9,100
assertions. Before/after profiles (`7e0340d22bad` / `9c7b7334f76d`) confirm that
the queues become empty, but all three target inputs still time out.

The fresh comparison covered **all 48 actual QF_NIA inputs** (24–47 and
104–127), not the older mixed-logic "linear96" subset. EOS `25abad104e9f`
records **23→22 verified results**, zero gains and one loss: primary 125,
`calypto/problem-000123.cvc.1.smt2`, changes from independently confirmed UNSAT
in 21.798 s to timeout. Verified PAR-2 worsens 3125.931→3215.507 s. There are
no opposite verdicts or invalid models. The variant is **rejected**; no full160
or production PR follows. Retain `perf/pending-theory-progress`, commit
`0f6d15c3bb08578718662a91f885a11c79d134cc`, frozen CLI SHA-256
`73994944b6919e0586443f69679d9baaebba4d7ef8783ef7009867cdb0dbb577`
and `core-r274`/`targets-r274` evidence. Queue delivery alone did not address
the measured solving gap; no claim is made about its causing older regressions.

The last applied server overlay is `source-r274.tar.json`. A subsequent overlay
must restore its abandoned NIA changes using `package_overlay.py --since`.
Continue from the qualified R264/main source and binary, not this experiment.

### Rejected eager monomial boundary context (R276–R279)

The old helper fails the mixed-boundary unit reproduction (EOS `436ed44afc14`):
`a,b,c` in `[0,1]`, `a+b=1`, `ab=ac=0`, `bc=1` require the mixed assignment
`a=0,b=c=1`, which its coherent whole-cover corners miss. R278 adds a generic
balanced candidate traversal and one incremental monomial relaxation, but its
eager quotient-chain expansion is **not selected**. It passes 1,694 unit tests /
801,317 assertions, 68 targeted tests / 154,998 assertions, and 32 independent
mixed-boundary fixtures. Both Z3 and cvc5 check all fixture decisions and replay
all 16 SAT models; those fixtures add no primary-suite solves or QCP programs.

Fresh NRA32 (EOS `ba33cd60d1f4`) verifies **20→19** results, zero gains, losing
SAT150 (`zankl/matrix-3-all-2.smt2`): baseline 0.625 s, candidate timeout.
Verified PAR-2 worsens 1455.632→1575.366 s. Same-round Z3 verifies 25; there are
no wrong verdicts or invalid models. Build EOS `156d24bb9270`, fixture checks
`83f5c292af30`, and diagnostics `619c15082cd3`. Source commit
`c4bdd84ccdafc4891c2010437f2020db01ebcd9b`; CLI SHA-256
`c831a9d06958e5854aacc79da63c4986f6151cec5375bef74083174776853fcf`.

The profile identifies avoidable construction work: 150 has 27 cover parameters
but exhausts the 20 ms allocation after only four choices and 518 row definitions.
149 similarly stops at depth 18 of 28. The next implementation should activate
only whole atoms whose current residual is affine, retaining one local context
and original-model validation. It must be qualified independently; neither the
new reproduction nor unit success establishes a benchmark gain. No full160 is
run for the rejected variant. Its overlay is `source-r278.tar.json`.


### Unselected lazy affine boundary context (R280/R281)

The revision activates only complete atoms that become affine under a selected
prefix. On 150 it reaches all 27 parameters using 87 definitions instead of
exhausting the allocation after four choices / 518 definitions. All 1,694 native
tests / 801,317 assertions, 68 targeted tests / 154,998 assertions and 32 mixed
fixtures pass; both engines replay all 16 SAT models. It restores 150 but adds
no solves over qualified R264: fresh NRA32 is **20→20 verified**, zero gains or
losses. PAR-2 changes only 1454.170→1454.076 s (0.095 s), insufficient benefit.
There are no wrong verdicts or invalid exported models. At R280 it remained
**unselected**, without a full160 or production merge. The user subsequently
requested sequential integration; R288/R290 below qualify its general capability
without claiming a primary-suite performance gain.

Source `3241ebfc875e51193c59425f8e4821c2eb6e3ab4`; frozen CLI SHA-256
`0b08d84767e484a9175c8ad20692e0f9f6fb6ee347a110f22b7047d06cdd5fd6`.
EOS build `4b6288dbf67c`, NRA `45f2ecadfe8a`, fixtures `a284c82eed1d`, profiles
`751526aa9793`. The last experimental overlay is `source-r280.tar.json`;
restore it explicitly when returning to the selected R264/main source.

## Original-input congruence certificate (R284/R285)

The last original R101 unconfirmed result, UNSAT115 (`ps6.c_7.smt2`), now has
an independently checked certificate anchored to its unchanged original SHA-256
`02a58b11df8951543940a1090a140592e24de41dcaeb6470e7a50d42e804be64`.
Together with R110's nine independent checks, this closes all ten original
R101 confirmation questions. Earlier tables retain their then-known evidence.

`tools/soundness/polynomial_mod_certificate.py` parses the original single-query
integer input, expands simultaneous lets, and accepts only a positive conjunct
`not (= (mod P m) 0)` with a nonzero constant modulus. For this query,
`P(y) = 10*y^6 + 6*y^5 + 7*y^4 + y^2` is zero in every residue class modulo 12.
Integer polynomial congruence makes this a proof for all integers, including
negative values. It is not bounded sampling. The verifier checks every row by
both Horner evaluation and direct source-AST evaluation, using Python integers
independently of Xolver's kernel. Zero divisors, unsupported scopes, partial
residue tables, source mismatches and corrupted witnesses are rejected.

Reproduce with the original benchmark file and the committed certificate:

```sh
python3 tools/soundness/polynomial_mod_certificate.py check \
  /path/to/ps6.c_7.smt2 docs/audit/ORIGINAL_UNSAT115_MOD_CERTIFICATE.json
python3 -m unittest discover -s tests/tools -p test_polynomial_mod_certificate.py
```

Panda1/ExperimentOS passed all 11 certificate tests, 1,689 native tests /
801,249 assertions and 916 regressions. Of 38 acceptance tasks, 37 passed at
initial limits. The remaining task preserved one Xolver 5-second generated-case
timeout; that identical input rechecked UNSAT in 0.084 seconds at the common
60-second budget, with Z3 independently UNSAT in 0.041 seconds. This recheck is
correctness evidence, excluded from fixed-suite performance scores. The
remaining 127 cases and all 64 models in that task passed their original checks.
Theory differential checks replayed 703 models without disagreement.

Both frozen executables are byte-identical to qualified R264. Supplementing
R266's original timed observations with this certificate changes its verified
baseline/candidate counts from 89/91 to **90/92**; Z3 stays **115**. Verified
PAR-2 totals become 8704.145 / 8473.629 / 5609.677 seconds respectively.
**No new algorithmic solve or timing improvement is claimed by this stage.**
The independent protected sets remain unused; the two qualified QCP development
programs are unchanged.

Evidence is committed in
[the source-certificate stage record](ARITHMETIC_ORIGINAL_MOD_CERTIFICATE_STAGE_20261028.json)
and [the certificate](ORIGINAL_UNSAT115_MOD_CERTIFICATE.json). EOS identities:
build `efcc8d02605b`, acceptance `fa471d751a92`, interval recheck `9289099bb060`,
and final evidence audit `75362afd43bf`. An initial audit started before all
acceptance records existed and failed; it made no solver or scoring change.
The final audit checks 40 native/recheck runs on 38 physical cores without
lease overlaps. No extra server archive is a delivery requirement.

## Mixed boundary propagation (R288/R290/R293)

The user requested sequential integration after the initial neutral NRA32
experiment. This stage qualifies the lazy affine implementation as a general
capability repair. The earlier eager monomial variant remains rejected.

A theory-independent finite candidate traversal balances every local push/pop,
including rejection, interruption and successful model extraction. The theory
supplies admissible candidates, propagation and a complete-model checker. The
arithmetic adapter reuses one private simplex context, activates an original
atom only after its whole residual becomes affine, and withdraws its bounds
and activation state on backtracking. It now finds mixed parameter endpoints
such as `a=0,b=c=1` for `a+b=1, ab=ac=0, bc=1` on `[0,1]`. Failure never exports
UNSAT. Integer scaling is separate; public APIs and the verified LRA/LIA root
backtracking policies are unchanged. Production integration remains pure NRA.

Panda1 qualification passed **1,694 tests / 801,317 assertions**, 36 targeted
tests / 146,307 assertions, all **38 acceptance tasks / 917 regressions**, and
703 model replays in the theory differential suite. All 32 generated mixed
fixtures pass both independent solvers, including all 16 SAT models. Combined
source qualification also passes architecture, standalone-evidence and the
complete Python regression harness, and checks the original UNSAT115 certificate.

Fresh frozen fixed160 uses 60 seconds, one leased physical core and 16 GiB per
solver invocation. With the independently checked original-input certificate:

| Version | Raw decisions | Verified decisions | Verified PAR-2 total (s) |
| --- | ---: | ---: | ---: |
| Qualified R264 baseline | 92 | 92 | 8469.997 |
| Lazy boundary candidate | 92 | 92 | 8472.375 |
| Same-round frozen Z3 | 124 | 116 | 5533.482 |

There are **zero verified gains or losses**, opposite verdicts, invalid exported
models, solver errors or memory failures. Candidate time is slightly worse by
2.378 seconds overall; this does **not** establish a performance improvement or
superiority over Z3. Candidate has 67 timeouts / one unknown; baseline has 68
timeouts. QCP remains two qualified unique development C programs, without a
new end-to-end coverage/timing claim. Neither independent protected set was used.

The benchmark harness now charges process creation to the existing absolute
wall budget, records launch/wait time, enforces the exact EOS CPU lease, and
rejects material budget overruns instead of scoring them as solver gains.
Ten timing/summary tests pass on Panda1. Initial R288 is superseded because of
wall overruns and one EOS timeout. R290 preserves one invalid index-5 observation
(283 seconds); its only protocol-failed case is retried with the **same driver,
versions, input and limits**, all three solvers sharing the retry's physical
CPU. The first protocol-valid retry is retained regardless of verdict, and both
Xolver versions return SAT with checked models. Original invalid records remain
available. No solver change, filename heuristic or answer-based selection is
introduced for this retry. The cause of the exceptional wait remains unresolved;
a separate baseline diagnostic on another leased CPU returns SAT in 6.298 s.

The [stage record](ARITHMETIC_BOUNDARY_PROPAGATION_STAGE_20261028.json) records
all 160 accepted report hashes, the superseded data, source inventories and 234
build/comparison/retry/acceptance/tooling/fixture leases without physical-core
overlaps. Native code is `3241ebfc875e51193c59425f8e4821c2eb6e3ab4`; timing
validation is `6fa40d7809261ba8c07d6c1399a933f8013625fa`. CLI SHA-256 is
`0b08d84767e484a9175c8ad20692e0f9f6fb6ee347a110f22b7047d06cdd5fd6`;
SV remains `99130012b880f255cd8bbaf456d4031d07649792c83c430acb5649a547bb89ef`.

EOS: build `97160349ae0d`, formal `db06c3224f3c`, retry `d898ed180e00`,
acceptance `e56938f8b97c`, timing tests `255a1a5d166c`, combined qualification
`03466fdb3066`, final audit `823a2f824d36`. The last applied source overlay for
this qualification is `source-r292.tar.json`; use it with `--since` for the next
server update. No extra server archive is a delivery requirement.

PR55's original-input checker was merged as `15586431` after both
[PR CI jobs](https://github.com/fuqi-jia/Xolver/actions/runs/40651147379)
passed; its [main CI](https://github.com/fuqi-jia/Xolver/actions/runs/40653122590)
is the sequential integration checkpoint before merging PR54.

## Main delivery receipt and unselected root-stop experiment (R294–R297)

PR55 merged as `15586431`; both PR CI jobs (`40651147379`) and both main CI
jobs (`40653122590`) passed. PR54 subsequently merged as `08b99eaf`; both
final-head PR CI jobs (`40654254640`) and both main jobs (`40656544660`) passed.
These are the qualified GitHub delivery checkpoints, without an additional
server archive requirement.

R294 reproduces unnecessary encoding after a known permanent SAT contradiction:
one new bounded-prefix test returns unknown after an unrelated polynomial
exhausts its encoding budget. R296 adds a conservative permanent-inconsistency
query to the common SAT interface and stops both bit-blast clients after a
known root conflict. Overflow remains distinct from a logical contradiction;
assumption-only UNSAT must not become a permanent conflict. All **1,698 native
tests / 801,334 assertions** pass. The frozen CLI is
`fd37e61a74fe4709e0570d675565a6300c9fc22c9248f1b40856006555cea413`.

The actual 48-case NIA observation contains **no gained decisions**, six
protocol-invalid budget overruns (30–35), and one unmatched result at 31:
baseline SAT in 1.460 s, candidate timeout with an invalid 74.512 s observation.
No opposite verdict or invalid exported model was seen. This is **not a formally
qualified coverage/PAR-2 round**; the invalid rows and possible loss are retained.
No full160 or production merge is justified. The standalone root-stop experiment
is closed without a performance claim. Its implementation remains an experimental
base for further proof-scope work, not selected production code.

The paired profile explains the limited opportunity: later root conflicts occur
after approximately 16,962–16,968 of 17,081 constraints. Stopping this short tail
does not remove the dominant repeated construction across bit widths. Continue
by testing completeness of the actual refutation footprint and core-guided width
refinement; those are hypotheses until separately reproduced and qualified.

Evidence: reproduction `1cda2a8bd9f2`, native build `0cffecdebcbb`, NIA48
`c540b543de9e`, profiles `0a332286213c`, and frozen source
`c5d3b9e0267666980a9ec4e82a16bbde40db05f1`. Server overlay for this experiment
is `source-r296.tar.json`. Neither protected set has been accessed.

## Failed-assumption scope and width experiments (R300–R309)

These branches remain experimental; qualified main is still `08b99eaf` and
frozen CLI R280. No new full160 score or production merge is established here.

R300 (`3fe3f2b02ec5`) reproduces a completeness gap: `x*x=2`, `0<=x<=2`,
`x+y-z=0` returns unknown because y/z are unbounded, although the contradiction
only needs x. R302 (`ac8080e0`) encodes completed predicates as assumptions,
maps failed assumptions to source/domain support, and requires justified finite
domains only for that support. SAT still requires a complete encoding and exact
model validation. Overflow cannot assert unfinished gates or predicates.

R302 passes **1,703 native tests / 801,355 assertions**; CLI SHA-256 is
`e8711cd3efbb80b21462343ffc0e6840737a6c477e3dcec87a34d41fe591ebd0`.
Its selective width refinement has one independently confirmed, protocol-valid
added decision at index 40 (`UltimateAutomizer/gauss_sum_true-unreach-call.i.smt2`):
baseline timeout 60.040 s, candidate UNSAT 43.322 s, Z3 UNSAT 0.168 s. Original
input SHA-256 is `d25714f4c95ce2bc5fb613fe3807d43875a48ed8fda1a97d68757345ca23522e`.
This is a single paired observation, not an accepted 48-case score: indices
27/29/31/32/37 overrun the wall protocol; 24 has an infrastructure relaunch and
an immutable-output collision; 106 reaches the EOS timeout without a final
report. Preserve all original records. R302 acceptance is 37/38, with two NIA
240-second timeouts. Fresh paired checks of those exact inputs return correct
results with both frozen versions in 0.03–0.07 s, including independent SAT model
replay; they do not erase the initial failures.

The selective policy also has a reproducible search regression: independent
`x=2^64`, `y=2^64` exhaust the shared seven-attempt budget and return unknown.
R306 first reproduces that failure from `source-r304.tar.json`, then restores
simultaneous refinement (`e11de3a2`). All **1,704 tests / 801,358 assertions**
pass, including 32 targeted cases. CLI SHA-256 is
`24698ee89ea0d5cd62a834f2e9e747100188ce75ad85c229dd7fccf0012ec449`.
The four-case fresh comparison does not select this variant: 31 matches verified
SAT, 40 times out with both versions, and 44 loses baseline UNSAT 45.011 s to a
candidate timeout. Index 123 has an invalid 80.152-second baseline timeout and
cannot count as a gain. Acceptance finishes 35/38: an Xolver generated-query
timeout, a Z3 model-replay timeout, one LIA timeout, and a QCP arithmetic-check
timeout in the unchanged SV binary remain recorded. No opposite verdict or
invalid model was found in the inspected failure records. This variant is
closed without a full160 rerun or merge.

R308 (`01d6ceab`) next tests sharing SAT state and literal-keyed gate definitions
across widths within one query. Low bits persist, high bits are added, current
facts are assumptions, and width-dependent polynomial caches are rebuilt.
Uniform widths and attempt limits remain; a new signed-refinement test checks
that low bits formerly denoting -1 can denote 3 in the wider leaf. Native
qualification passes in EOS `eadd23a019f4`: **1,705 tests / 801,362 assertions**,
using `source-r308.tar.json`. Frozen CLI SHA-256 is
`d7e813c75da5d1c4e2c93762364b442fb799ec25ae2145e2f1ec4be316492904`.
The five accepted paired development observations establish no added or lost
solve. Cases 44 and 123 improve from 48.73 to 33.62 seconds and 47.45 to 27.58
seconds; 40/114 still time out. Original empty-CPU launches and an over-budget
observation remain recorded separately. Evidence: pilot `5497e15e0145`, first
protocol-valid retries `5958cd25add3`, profiles `9b5da2819172`. This local speed
benefit alone did not qualify a production merge or a full160 score.

Evidence: R302 build `cd028a4720a1`, NIA48 `d89b89d50a21`, profiles
`9d50b89a6627` / `b70de5e0449e`, acceptance `c23b54c5604a`, paired regression
recheck `04b5bca03f88`; R306 build/reproduction `f82a12bc7a15`, four-case
comparison `42daff1adcc3`, acceptance `c5be845d4e8b`. Budget diagnostics
(`b9bdfd18`) distinguish late timeout notification from cleanup: observed large
overruns occur before notification, with millisecond cleanup. File-backed output
capture does not establish the cause of those overruns. Other root-owned fuzzers
were observed consuming cores; their role in each timeout is unproven. QCP stays
at two qualified unique development programs. Neither protected set was used;
an additional server archive is not a delivery requirement.

## Current-domain and complete-reason repair (R312–R332)

R312 (`e1d24fe79f7c`) first reproduces four failing native cases: the early NIA
bit-blast stage misses current bounds, reset/backtrack retains obsolete domains,
a product-derived upper bound omits its divisor lower-bound premise, and a fixed
integer unnecessarily exhausts a one-gate encoding budget. Five assertions fail
before the implementation. R314 repairs the current-prefix domain lifecycle,
retains all premises of product-bound propagation, and encodes explained fixed
domains as constants. Source commits are `620be852`, `f2a29d2f`, `e6bf8dcd`, and
`1e318da1`; the candidate also includes the scoped-refutation and shared-gate
implementation above. SAT still requires exact whole-query model validation.

For example, `x*y=10`, `x>=6`, `y>=2` is inconsistent, but omitting either lower
bound permits a model. The new unit test catches the invalid internal conflict
explanation. Four original/removed-premise SMT checks agree with independent Z3;
all three SAT cases have independently replayed models. This reproduces an
explanation bug, not an observed opposite whole-input solver verdict. Evidence:
`e215592be97d`, first missing-lease retries `bf6b9ab75514`.

Native qualification `7a47b2ba6f79` passes **1,709 tests / 801,383 assertions**,
including 38 targeted cases / 323 assertions and three CTest checks. Source is
`source-r314.tar.json`, head `1e318da14f96c73bbe26fabe14041f9288ef3a7f`.
Frozen CLI SHA-256 is
`eaa3b5b87c2b5df589729a728a5e6bc3d4bb4a0b23ca9205f1baea0581874567`;
SV remains byte-identical to qualified main.

Fresh NIA48 R318 (`db9f3de0f7ed`) completes all 48 physical-core leases without
protocol errors, opposite verdicts, or rejected exported models. With the
previously checked original-input certificate for 115, verified solves are
**main 23 / candidate 24 / Z3 30**; verified PAR-2 is **3086.186 / 2953.553 /
2237.162 seconds**. The sole coverage change is index 123: main timeout 60.092 s,
candidate UNSAT 22.607 s, independent Z3 UNSAT 0.367 s. Main solved this same
input in other paired rounds, so this is a round-dependent budget improvement,
not newly established logical capability. Four Z3-only UNSAT results remain
unconfirmed within budget. The certificate is supplementary truth evidence,
not a fabricated timed oracle observation.

Full160 R320 (`4d95a146ec30`) finishes with the same frozen versions and
60-second / one-physical-core / 16-GiB protocol. Four original rows (8/24/32/42)
overrun the wall budget and are excluded. Their first unchanged-version paired
rechecks are retained from `9f97d11f73bd`, `2d30731b5b2f`, and `8cd0f1970d29`.
Verified solves are **main 92 / candidate 92 / Z3 115**; verified PAR-2 is
**8468.816 / 8426.471 / 5614.750 seconds**. Candidate coverage by logic is
LIA 32/48, NIA 24/48, LRA 16/32, NRA 20/32, matching main exactly. There are
zero added or lost solves, 67 timeouts and one unknown for each Xolver version,
and no opposite verdict or rejected exported model. Overall PAR-2 improves
0.50% in this round; NIA alone improves 2988.311 to 2935.691 seconds. This is
not evidence of overall superiority to Z3 or a full-suite coverage gain.
Z3 has 124 raw decisions, with nine still unconfirmed in this round.

Server acceptance R314 (`63deb994f18d`) initially passes 36/38 tasks: partial
integer arithmetic has five oracle timeouts; interval checks have an Xolver
model-query failure and a verdict timeout. First paired rechecks R322
(`e5796f92791a`) keep the original seed/count/five-second budget and pass with
both frozen versions: 27 partial-arithmetic cases and 128 interval cases,
including model replay. Original failures remain recorded. All **921
regressions**, **703 theory-model replays**, and existing QCP checks pass.

Final source/result/lease audit R332 (`f6e4c98d5c69`) passes; evidence is
`stage-r332.json`, SHA-256
`464be41c1da1db24656aebefbe35b9da2005d69db3b562439f5776193cef2ed6`.
All 204 audited tasks have physical CPU leases and disjoint execution envelopes.
An earlier audit (`ab66920e6e5a`) incorrectly treated delayed collector end
timestamps as process exit times; its failure is retained. The corrected audit
uses launcher-script creation through the executor's post-workload end file,
and records the four collector-timestamp overlaps separately.

Delivered in [PR #56](https://github.com/fuqi-jia/Xolver/pull/56), merged as
`2db4ca3e992d67b4574254c1ab6193aec4e8131e`. Both jobs passed in
[PR CI](https://github.com/fuqi-jia/Xolver/actions/runs/40687532135) and
[main CI](https://github.com/fuqi-jia/Xolver/actions/runs/40691217044).
Qualified main now uses the frozen R314 CLI above. QCP has no additional
qualified end-to-end program coverage from this arithmetic stage. Both protected
sets remain unused; no additional server archive is a delivery prerequisite.

## Shared QCP process-budget correction (R334–R336)

The QCP backend previously granted a full communication timeout after process
creation and could accept an exit-zero UNSAT answer observed after its deadline.
Its program audit also accepted over-budget or non-finite query times. R334
reproduces six failing assertions against the unchanged implementation in EOS
`f9cf2203bc68`; no timed program score is inferred from this reproduction.

Commit `07766264` extracts the strict arithmetic process-budget implementation
into `tools/process_budget.py` and reuses it in both arithmetic comparison and
QCP discharge. Process creation consumes the same deadline; late answers cannot
produce proof candidates. QCP audit separates independently verified programs
from backend-budget qualification and rejects invalid budget evidence. The
existing arithmetic timing semantics are retained.

Panda1 qualification R336 (`b734810dd1d9`) passes **26 QCP tests**, **five process
budget tests** (including a real detached output holder), **seven comparison
summary tests**, the regression-harness CTest, and four actual Xolver/Z3 query
smoke checks. Native C++ source and both frozen binaries remain byte-identical
to R314, so no native rebuild or full160 repeat is attributed to this Python
change. Evidence: `qcp-budget-r334/repro.json`, `qcp-budget-r336/report.json`,
and `source-r336.tar.json`. The commit was rebased onto delivered PR56 with an
identical file tree. This corrects the comparison protocol; it adds no solved
SMT input or verified-program count. Neither protected set was used.

## Delivery receipt and explained affine endpoints (R346–R355)

PR57 merged as `b15551b37d9154856b0c5671a971ac05dd919ad8`.
Both jobs passed in [PR CI](https://github.com/fuqi-jia/Xolver/actions/runs/40697097275)
and [main CI](https://github.com/fuqi-jia/Xolver/actions/runs/40702037717).

The presolve-domain transfer experiment R338–R345 remains unselected. It passed
1,714 native tests, but the first valid five-case comparison solved three with
each version: PAR-2 274.724 versus 277.424 seconds. Its sole apparent gain came
from an invalid baseline timing; the first unchanged-version paired retry
removed that gain. Original failures and superseded observations remain in
`stage-r345.json`. This was not a propagation memory-pool experiment.

R347 identifies a different omission: early NIA domain inference handled only
single-variable atoms and zero-offset `x=y`. Active rows such as `x=2y` and
the two inequalities expressing `i_next=i+1` left derivable endpoints absent.
R348 (`dcf6b8e0a3f5`) reproduces missing bounds through an affine dependency
chain. Core commit `1dbbc01d` replaces the narrow second pass with a shared
linear worklist. It uses exact rational endpoints, strictness, complete row and
endpoint guards, per-variable sort-aware integer rounding, and a work budget.
Only rows affected by strict progress are revisited. NIA consumes the shared
engine before early bit-blasting; LRA/LIA backtracking policies are unchanged.

R350 native qualification (`821b38f26614`) passes **1,714 tests / 859,636
assertions**, including **56 targeted tests / 86,214 assertions**, and three
CTest checks. Frozen CLI SHA-256:
`b337850528f80c31d0a364a097bb4147181618e989df37173741b1d2f8831fca`.
SV retains `99130012b880f255cd8bbaf456d4031d07649792c83c430acb5649a547bb89ef`.

The [NIA stage record](LINEAR_BOUND_PROPAGATION_STAGE_20261028.json) audits all
48 fixed NIA cases (EOS `b80b4aafd8e0`): **24 / 25 / 29 independently verified
solves** for main / candidate / Z3, with verified PAR-2 **2938.758 / 2837.254 /
2313.667 seconds**. Z3 has 34 raw decisions; unresolved results stay excluded.
The existing original-input certificate for 115 was checked again and attached
as supplementary truth, without changing timed observations. The only gain is
index 40, `gauss_sum`: main timeout, candidate UNSAT 20.042 s, Z3 UNSAT 0.217 s.
It repeats the five-case pilot gain. No solve was lost; no wrong verdict,
rejected model, or protocol-invalid row occurred. Instrumented diagnostics show
145 bounded/fixed variables instead of four and zero allocated SAT variables;
these diagnostic runs are excluded from timing scores. All 38 unique acceptance
items pass. Three duplicate submissions failed before executing checks because
an older spec was parsed during upload; their original valid targeted results
are retained explicitly in the provenance.

The frozen full160 comparison R354 (`7847f8d0c8cd`) and final audit R358
(`2085da11c5ee`) pass. The [full comparison record](LINEAR_BOUND_FULL_COMPARISON_STAGE_20261028.json)
reports **main 92 / candidate 93 / Z3 115 verified solves**, with verified PAR-2
**8419.877 / 8322.680 / 5609.762 seconds**. Xolver changes from 52 SAT / 40
UNSAT / 68 timeouts to 52 SAT / 41 UNSAT / 67 timeouts; neither has an unknown
in this round. Z3 has 124 raw decisions, with nine unresolved decisions excluded.
Index 40 is again the only gain: candidate UNSAT 20.078 s versus main timeout
and Z3 UNSAT 0.218 s. No solve is lost, no verdict/model is rejected, and all
160 original paired rows satisfy the timing protocol; no retry is substituted.

The lease audit checks 254 task envelopes across the formal round, NIA round,
pilot and acceptance runs, with one allocated physical CPU per task and zero
physical execution overlap. All 38 unique acceptance items remain valid; failed
duplicate submissions are explicitly retained. R359 corrects R355's omitted
per-logic certificate counter adjustment; total NIA scores and every timed
observation are unchanged. The original aggregation is retained on Panda1.

This establishes one additional verified solve in the primary development suite.
It does not exceed Z3. Neither protected set has been used. The C++ code is in
[PR58](https://github.com/fuqi-jia/Xolver/pull/58), merged as
`0d937a71524fad58e8780cd2d3e72b2d007de320`. Both jobs passed in
[PR CI](https://github.com/fuqi-jia/Xolver/actions/runs/40708236349) and fresh
[main CI](https://github.com/fuqi-jia/Xolver/actions/runs/40711539985).

## Eager reuse of affine endpoints (R360–R378)

The next omission was in whole-formula eager bit-blasting: it collected only
single-variable unit-coefficient bounds, even after the NIA theory path gained
general affine propagation. On fixed index 40 it spent about 19.8 seconds
building circuits before the theory path proved UNSAT. R360 (`27977fbb21db`)
also reproduces a missing exact model beyond the uniform width cascade.

Core commit `eae83750` reuses the same linear worklist over positive root
conjuncts, including chained equalities and signed affine inequalities. Empty
guard sets explicitly denote unconditional facts; the DomainStore client
continues to omit unexplained endpoints. Proven fixed integers become constant
bit-vectors. Boolean branch predicates remain conditional, exact candidate
validation remains mandatory, and this eager arm still never claims UNSAT.
LRA/LIA backtracking policies and public API semantics are unchanged.

The [NIA qualification record](EAGER_AFFINE_NIA_STAGE_20261028.json) records
R362 (`2ae28933fd26`): **1,719 native tests / 859,661 assertions**, 61 targeted
tests and three CTest checks pass. All 38 acceptance items qualify. The affine
item originally had a five-second Z3 model-replay timeout; the first paired
recheck at the same seed, count and five-second budget passes with both frozen
versions. The original failure remains recorded. CLI SHA-256:
`663ea64fbf924b1312d1be498d504b00a10b4f9671799621debcd4638a861988`;
SV remains `99130012b880f255cd8bbaf456d4031d07649792c83c430acb5649a547bb89ef`.
The source was rebased onto PR58's squash with an identical entire file tree.

The 48-case NIA round verifies **25 / 25 / 29** solves for delivered main /
candidate / Z3, with PAR-2 **2834.943 / 2812.978 / 2312.683 seconds**.
The valid slow five-case pilot observation for index 123 (21.880 to 49.450 s)
is retained. Separate diagnostics did not reproduce it; its cause is unresolved.

The [full160 audit](EAGER_AFFINE_FULL_STAGE_20261028.json), EOS `efccf1b6610b`,
verifies **93 / 93 / 115 solves**, PAR-2 **8309.014 / 8298.646 / 5618.248 s**.
Both Xolver versions have 52 SAT, 41 UNSAT, 67 timeouts and no unknowns. There
are no gained/lost solves, opposite verdicts or rejected models. Index 40 falls
from 20.067 to 0.167 s; index 123 takes 11.449 versus 11.533 s in this round.
Five protocol-invalid original rows and one incomplete outer-timeout row are
retained. Their first unchanged-version paired retries replace only those
invalid observations; the apparent original gain at 19 disappears. Timed
observations and the original-input certificate for 115 remain distinct.

Unrelated host workloads were observed during this round. The lease audit
establishes non-overlap among the recorded ExperimentOS tasks, not exclusive
use of the entire server; small timing differences may include host noise.
This establishes a repeatable local encoding improvement, with no increased
development-suite coverage or claim of overall superiority. Neither protected
set was used. [PR59](https://github.com/fuqi-jia/Xolver/pull/59) merged as
`0fa0f87bdbd6980e1266e34912daf6dbd1974c12`. Both jobs passed in
[PR CI](https://github.com/fuqi-jia/Xolver/actions/runs/40721530284) and fresh
[main CI](https://github.com/fuqi-jia/Xolver/actions/runs/40724656537).

## Binary integer solving, model reuse and aggregate refutation (R400/R424/R442/R460)

Qualified core commit: `a643d62b11c4b63e49f97bf1a9a0003fefaecbba`.
The [initial context record](BINARY_INTEGER_CONTEXT_STAGE_20261029.json) and
[final full160 audit](BINARY_INTEGER_AGGREGATE_FULL_STAGE_20261029.json) retain
both the gains and the intermediate regressions.

Root facts proving every used integer belongs to `{0,1}` enable fully reified,
exact pseudo-Boolean thresholds over the complete Boolean formula. Signed and
large coefficients, complementary literals and binary polynomial products are
handled without width escalation. Applicability is structural; this SAT-only
arm still validates every original assertion with exact arithmetic.

Two general quadratic costs prevented large cases from completing. Parser
source positions rescanned the entire input prefix per command (141/143 and
141/142 profile samples). A line-start index preserves source-location semantics.
After that fix, model validation rebuilt a 19k/26k-variable assignment for each
of 105k/141k atoms. An immutable polynomial evaluation context now binds it once;
integer and rational clients retain exact results and missing-binding checks.
The initial partial-assignment crash is retained as rejected qualification R418;
the original test passes after explicit support checking and value ownership.

The intermediate candidate solved two extra SAT cases but delayed two easy
UNSAT cases by about 20 seconds. R440 found 48/48 and 49/49 samples in SAT
search, with encoding taking only 2 ms. Shared linear aggregation now sums
asserted inequalities using exact positive multipliers and retains a checkable
contradiction and every premise. The eager arm yields to arithmetic; the NIA
domain reasoner can emit the explained conflict. Strict rational, scaled,
conditional and feasible-witness controls pass. The targeted round restores
20.006→0.220 s and 20.007→0.166 s; diagnostics show 29/27-row certificates
`0 <= -1` and no SAT search. LRA/LIA backtracking policies and public API
semantics are unchanged. There is no new runtime gate or external oracle.

R442, EOS `54f07ddcba2b`, passes **1,737 tests / 876,303 assertions**, 79
targeted tests, all 63 parser CTests and three architecture/evidence/harness
checks. All 38 R450 acceptance items pass. An additional **192 distinct**
LIA/LRA/NIA cycle/guard cases agree with Z3 and cvc5; all **156 SAT models**
have both independent replays. One original target exceeds its budget and one
QA batch records two Z3 timeouts while unrelated root workloads occupy leased
CPUs. Their first unchanged-input/version/budget rechecks pass; original records
are retained. No valid slow observation is replaced: full160 index 18 remains
46.478→50.709 seconds.

Fresh full160 R448, EOS `48450ccfd508`, has 160 complete, protocol-valid rows,
with **main 93 / candidate 95 / Z3 115 verified solves** and verified PAR-2
**8295.528 / 8111.836 / 5616.976 seconds**. Candidate results are 54 SAT,
41 UNSAT, 65 timeouts, zero unknowns; there are two gained SAT cases (indices
2 and 97, 37.301 and 34.391 seconds), no lost solves, opposite verdicts or
rejected models. Each gain has an independently replayed model. Z3 has 124 raw
decisions; nine unresolved confirmations remain excluded. The original-input
certificate for 115 is checked independently without changing timed results.
The earlier R428 round has its own 116 confirmed Z3 results; do not transfer
that count between rounds.

Frozen CLI SHA-256:
`6ce2bc442b9576124956deb73a5f9c5cd9cae64f26512ff38dfc90f6ae948aa2`;
SV: `74fe8d8fe48db4b9745ae466d9128fc25adab870765694dc09f6cc8ecba2d3af`.
R460, EOS `f94a0ac1341f`, checks source manifest, binaries, logs, input hashes,
models, the certificate and 221 physical CPU execution envelopes without overlap
among recorded tasks. This is not exclusive-host evidence. That stage applied
`source-r442.tar.json`; the latest stage below gives the current export cursor. Source and
binary qualification is sealed before subsequent documentation-only commits.

The later R486/R514 section records this implementation's final qualification
and delivery through PR60. Parser PR65 requires a reviewer;
ordinary and automatic merging are blocked, and no admin bypass is authorized.
Neither protected set was read or evaluated. This stage increases development
coverage by two, remains below same-round Z3, and establishes no real QCP
program-suite speed superiority. Continue toward the full SMT and program goals.

## Complete polynomial supports and affine equality blocks (R486/R514)

Qualified source: `d5e3c2a5d10413422dc603068b68558967b09f07`.
[The complete audit](AFFINE_EQUALITY_BLOCK_FULL_STAGE_20261029.json), EOS
`2e13cca6d84d`, binds source, frozen binaries, all original-input hashes,
independent checks and 229 physical CPU execution envelopes without overlap
among recorded tasks. Last applied overlay is **`source-r486.tar.json`**;
use it for the next incremental export. Later documentation commits do not
change the qualified executable.

`LibPolyKernel::variables` pruned coefficient traversal when a main variable
had already been seen. For `y + z*x*y`, it could omit `x`, although changing
`x` changes the value. Traversing every actual monomial fixes complete support
while preserving sorted variable IDs and caching. The same native diagnostic
source reproduces the omission before the repair and passes afterward.

The dependency repair alone caused a real search regression: the intermediate
candidate dropped from 95 to 94 verified solves. Its
[rejected performance record](POLYNOMIAL_SUPPORT_REGRESSION_STAGE_20261029.json)
retains the valid 60-second loss on index 158. The underlying model search
pinned a highly connected equality unknown, then sampled a finite grid that
missed the required exact rational value. For example, `a*r=1`, `b*r=2`,
`c*r=3`, with `a=5`, `b=10`, `c=15`, requires `r=1/5`.

The shared NRA/NIA search now retains a jointly affine block of equality
unknowns and samples the remaining monomial cover. Powers and products in
inequalities also constrain the block. One local simplex context completes
the unknowns; the existing 20 ms/work allocation, full original-polynomial
checks and integer admissibility remain. The native example now succeeds,
including signed and variable-order variants. Index 158 changes from a
60-second timeout in the intermediate version to **0.066 seconds**; the new
model passes independent replay. Profiling records 3 retained unknowns,
25 linear checks and 12 choices, finding a model in 1,175 microseconds.

R486, EOS `5080f2269d9a`, passes **1,742 tests / 876,581 assertions**, 93
targeted tests, 63 parser CTests and all three structural/evidence checks.
All 38 acceptance items pass using 36 original results and two full unchanged
rechecks of timeout-only failures. The original affine oracle/model timeouts
and ALIA timeout remain archived. Another **128** exact finite-domain cases
agree with Z3/cvc5, with both independent replays for all **76 SAT models**.

Fresh, frozen fixed160 results use 60 seconds, one EOS physical CPU and 16 GiB:

| Version | Verified solves | Raw decisions | Verified PAR-2 (s) |
| --- | ---: | ---: | ---: |
| Delivered main | 93 | 93 | 8305.014 |
| R486 candidate | 95 | 95 | 8114.580 |
| Same-round Z3 | 116 | 124 | 5524.035 |

There are two gained SAT cases (2 and 97, 33.791/34.247 seconds), zero lost
solves, opposite verdicts or rejected models. Candidate totals are 54 SAT,
41 UNSAT, 64 timeouts and one unknown (74, previously a timeout). Main's
index 158 takes 3.675 seconds versus 0.067 in the candidate. Valid slower
observations, including indices 4 and 123, remain in the audit. Eight
unconfirmed Z3 UNSAT results stay excluded; certificate 115 is checked
independently without changing solver times.

Of the initial formal submissions, 124 received empty CPU lists and failed
at `taskset` before running a solver. Their first correctly leased executions
complete the suite; all 36 valid original rows remain. Seven invalid target
rows have unchanged-version/budget rechecks. One intermediate target attempt
was interrupted by the outer deadline during model checking after external
pinned root workloads delayed it; its partial observations are retained too.
The final recheck excludes sampled external pinned physical cores through
EOS placement. No valid slow result is rerun away. This is not exclusive-host
evidence, and neither protected set was read.

Frozen CLI SHA-256:
`95b00d142d0e616263230f165fd6322dd88ec3cbcffe1bde1b7eb0d64e901e33`;
SV: `fed5b68160230b6bb372278e09c7e0088464e911ffce013dc91da080ceeadccf`.
LRA/LIA backtracking policies and public API semantics remain intact.
[PR60](https://github.com/fuqi-jia/Xolver/pull/60) merged as
`cb799c065bf7f13e0465a5622a560406a03871a8` after both jobs passed in
[PR CI](https://github.com/fuqi-jia/Xolver/actions/runs/40820715961). Both jobs
also pass in [fresh main CI](https://github.com/fuqi-jia/Xolver/actions/runs/40823193025).
The merged tree exactly matches the qualified PR head, including the later
documentation-only evidence commit. Parser PR65 still requires
review; no admin bypass is authorized. The candidate remains below Z3 and
does not establish QCP program-suite superiority.

## Independent fresh QCP development workflows (R462/R474)

[The paired record](QCP_INDEPENDENT_WORKFLOWS_STAGE_20261029.json) authenticates
two separate controller runs of the unchanged `max3.c`: new VC generation,
selected frozen backend, fresh proof development/checking, publication and
distinct canonical final-checks. Each backend covers all **4 original VCs**
and **12 external SMT queries**, with identical query hashes across runs.
Both canonical states reach `done`; EOS audit `691429f09c05` confirms complete
proof coverage and candidate identity.

The Xolver backend here is separately frozen **R442**, not R486. This adds no
new unique program: development coverage remains branch, GCD and max3, with
partial external coverage for GCD. The unchanged max3 contract proves the
return is at least each input with `emp`; it does not prove that the return
equals one input. Native internal QCP SMT calls remain opaque. Interactive
orchestration time and external query sums cannot establish a fair automated
end-to-end performance winner. A reproducible native whole-program timing
interface and the final independent program suite remain outstanding.

## Additional complete QCP development program (max3 R334)

[The max3 record](QCP_MAX3_QUALIFICATION_STAGE_20261028.json) authenticates the
unchanged original C body and its signed-input lower-bound contract for the
return value. All four original
VCs have complete proofs; each frozen R314 Xolver/Z3 backend supplies 12 UNSAT
queries. Group, parent, publication and fresh canonical final-check pass, followed
by separate program audits for each frozen backend. Their candidates match the
same Rocq-checked proof. The final-check EOS is `b1425a26c02d`; independent
audits are `a4c87f70584c`.

Unique qualified development programs increase from two to three: branch,
GCD and max3. GCD still has partial external-backend coverage. This is not two
fresh timed end-to-end runs or a fair program-suite comparison. The pinned
native QCP frontend and opaque internal SMT remain common; external query
counts cannot establish total internal calls. Neither protected set was read.

## Closed experiments and practical regressions

R178 replaced the square-cascade's ad hoc coefficient-Horner substitution with
the common exact polynomial substitution. Native 1,674 tests passed, but the
eight-case fresh comparison retained three verified solves with each version;
no gain was established. The candidate was restored without a production PR.
Evidence: `arithmetic-r103/core-r178` and `targets-r178`; EOS
`e27b9b56820a` and `3df6dfa99401`.

R179 tested necessary-endpoint checks before exact row propagation. All 1,675
native tests passed, including 128 signed missing-endpoint patterns. Across all
32 primary LRA inputs, both versions verified 16 results, without gains or
losses. PAR-2 changed 1955.272 to 1950.057 seconds (0.27%); the limited time benefit
did not close the solve gap, so the candidate remains unselected on
`perf/linear-propagation-feasibility` (`957daa83`). Evidence: `core-r179` and
`targets-r179`; EOS `1c435554817e` and `e3972dfcf374`. This was an arithmetic
eligibility experiment, not a propagation memory-pool rerun.

The LRA startup benchmark `tta_startup/simple_startup_10nodes.missing.induct.smt2`
completed SAT in three quiet repetitions at 10.94, 10.46 and 10.27 seconds with
LRA point preservation; the previous implementation timed out at 60 seconds.
Its exported model passed Z3 and cvc5 replay. Evidence: R90,
`validation/lra-model-r90-20261026/`.

Applying the same root policy to LIA caused a deterministic regression on
`65536*x + 196867*y = 16, y <= 7`: the old policy solved three repetitions in
0.035–0.044 seconds while the experimental policy timed out at 5 seconds.
An exact witness is `x=176344, y=-58704`. LIA retains its original root policy;
`tests/regression/lia/lia_affine_root_model_sat.smt2` protects this behavior.
Evidence: R86; the restored implementation passed whole-source R88 acceptance.

The per-call propagation memory-pool experiment is finished and excluded from
main. R92 whole-source acceptance passed, and R95 reproduced 78/160 decisions
with no observed wrong verdicts or errors. However, the same-core, alternating
order comparison over all 32 primary QF_LRA cases solved 15 with each binary:
PAR-2 totals were 2075.772 versus 2076.028 seconds, with median matched-case
speedup 0.991 and geometric mean 0.986. There is no measured speed benefit.
Evidence is retained in `validation/lra-storage-paired-r93-20261026/`,
`validation/full-acceptance-r92-20261026/` and
`validation/z3-gap-candidate-r95-20261026/`; source is retained on the local
`perf/lra-propagation-storage` branch and in `z3-gap-source-r91.json` plus its
overlay. Its frozen CLI SHA-256 is
`8c140f267454adc898731b81222593d5f11f4445ae51e7e3da8794859f859abf`.
The final source overlay restores the ordinary propagation storage.

## Unresolved limits and next-stage work

- The primary suite still has a substantial coverage gap against Z3. Broader
  speed superiority has not been demonstrated.
- `geom_offspring_0.499_PRAY.smt2` (primary index 157, SHA-256
  `d3941102878489abc44c6b3fafc7671a34c6d229ecf1820b0810e90dc61ef1cc`)
  is now solved and its model replayed in R264/R266. Earlier root-bracket
  compaction removed a GMP allocation abort but had not solved it on its own.
- `tests/known_gaps/nra/box_sector_joint_reasons.smt2` remains a known SAT case
  for which sound `unknown` is allowed by the explicit known-gap contract.
- General quantified PA/SL coverage and formal C++ end-to-end verification
  must not be inferred from these arithmetic certificates or passing CI.

A future performance stage should begin from the delivered binary and
source, profile the remaining propagation/search costs, and evaluate each change
with fixed inputs and identical budgets. Do not revive unsafe refutation
shortcuts, assume zero-divisor identities, cap propagation output based on the
consumer's accepted count, or reuse stale explanations across context changes.

## Complete GCD backend coverage (R588/R606)

[PR62](https://github.com/fuqi-jia/Xolver/pull/62), merged as
`e684332b932a14098d9df171b409535bcc423adb`, supports signed `Zgcd`/`Z.gcd`
and named/composed VCs. A shared UF receives valid finite ground instances of
nonnegativity, zero boundaries, symmetry and Euclidean remainder invariance;
this is not bounded guessing of GCD values. Missing instances can prevent
proof; SAT on the projection does not refute the C program. See
[the integration guide](../QCP_INTEGRATION.md).

Two fresh workflows preserve the original recursive GCD C body and exact
`__return == Zgcd(x,y)` contract. Both reach controller `done`, after independent
VC analysis, three proof groups, complete parent checking, publication and fresh
canonical replay. Each backend discharges **9 top-level VCs**, **3 auxiliary split
conditions**, and **34 actual external SMT calls**. Split conditions cannot
substitute for primary coverage. Mathematical closers pass unchanged; five
outer parent routes per backend are explicitly adapted to mandatory LLM/aggressive
entry, preserving generated candidates and route-repair evidence.

R598 passes 32 Python tests on Panda1. R604 independently checks all 50 sufficient
queries from 14 original definitions with frozen final Xolver, Z3 and cvc5:
150/150 UNSAT calls, 60 seconds/one leased physical CPU/16 GiB each.
R606 (`7e20f6379512`) authenticates both complete workflows and reports;
[the stage record](QCP_GCD_FUNCTION_STAGE_20261029.json) has SHA-256
`e787ea6893d6139ae1bdf9bcf8c5f63550ff7a4e4137172541b56f0730719969`.

GCD external-backend coverage is now complete. The development inventory remains
three unique programs: branch, GCD and max3. Internal symbolic-executor SMT stays
common and opaque. Interactive workflow/query sums do not establish an end-to-end
speed win. Neither protection set has been read or evaluated.

## Exact linear phases and decision interface (R596/R608)

[PR63](https://github.com/fuqi-jia/Xolver/pull/63) merges as
`db671329385edc343ada4a11a2787b9c3f903053`. LRA and LIA share exact model-point
evaluation in `LinearAtomManager`. This fixes the discarded infinitesimal in
`x > 0` at a positive-infinitesimal point and the rounded equality test between
`2^200` and `2^200+1`. These are heuristic phase evaluations, not entailments or
verdict certificates; no earlier wrong SAT/UNSAT result is asserted.

`Propagator::decisionSource(DecisionContext)` exposes `SatActivity` and
`TheoryModel` selection per request. Explicit unassigned `decide()` picks retain
priority; the default remains the existing theory-model selection. Full-model
checks and LRA/LIA backtracking policies are preserved. This is a research
interface, with no new default branching algorithm; see
[the interface guide](../DECISION_SELECTION.md).

R596 (`2929bdc10f0e`) qualifies source
`d4a2fe7aefcfbc4be23665aeee89ec35be51cc74`: 1,745 unit cases/876,668 assertions,
147 targeted cases, 63 parser tests and three structural checks pass.
R600 (`efa2273a1dbb`) passes all 38 server acceptance groups. Frozen CLI SHA-256:
`c919846a8c7b8880b28a43f7201499e0d761c27d74adf3615177b21b375f9284`.
The SV executable remains `fed5b68160230b6bb372278e09c7e0088464e911ffce013dc91da080ceeadccf`.

R602 compares frozen versions freshly on every fixed160 input, with 60 seconds,
one physical CPU and 16 GiB per solver. Original UNSAT115 retains its checked
original-input modular certificate. SAT results require independent model replay.

| Version | Verified | SAT | UNSAT | Unknown | Timeout | Verified PAR-2 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Previous main | 95 | 54 | 41 | 1 | 64 | 8105.846 |
| Exact phases/API | 94 | 53 | 41 | 1 | 65 | 8223.936 |
| Frozen Z3 | 115 | 66 raw | 58 raw | 0 | 36 | 5614.207 |

Nine Z3 decisions lack confirmation and are excluded. The only loss is verified
SAT59: previous main 3.376 seconds, candidate timeout 60.010 seconds. No new
solves, wrong verdicts or invalid exported models occur. Earlier negative
R582/R586 evidence remains immutable; the user explicitly retained the correct
calculation despite this performance regression.

R608 (`bdf65444c9e7`) authenticates the complete stage;
[the stage record](LINEAR_MODEL_PHASE_API_STAGE_20261029.json) has SHA-256
`5dfba3104f1954046d9715867180c1256e308e5f3d37653bc79d0646a22f59c0`.
This is a functional accuracy/API delivery. It does not meet the goal of beating
Z3, and no protection-set results are claimed. No extra current-main server
archive is required after GitHub CI.


## Paired linear propagation snapshots (R659/R664)

The [qualified row-snapshot implementation](LINEAR_PROPAGATION_ROW_SNAPSHOTS_20261029.json)
is based on main `07ea0c36`. It shares exact contribution sums and premise
multiplicities between adjacent lower/upper visits to one unchanged tableau row.
Non-basic endpoint updates invalidate the local snapshot; no cached state crosses
a theory check or backtrack. LRA/LIA backtracking and exact model phases remain unchanged.

R659 passes 1,762 unit cases / 876,943 assertions, 243 targeted cases and 63 parser
checks. A checked reproduction observes two visits, one snapshot build and one
reuse hit. R665's 37 regression, independent arithmetic/model, QCP and certificate
groups all pass on the frozen implementation.

Fresh R664 uses 60 seconds, one leased physical CPU and 16 GiB per solver/case.
Verified results increase **94 to 95**, with one added SAT (index59), no losses,
no opposite verdicts and no invalid exported models. Aggregate verified PAR-2
changes from 8220.612 to 8156.644 seconds. Index59 completes in 56.013 seconds;
three separate diagnostic repeats complete in 49.403, 47.361 and 47.227 seconds,
with independent exported-model replay; their timings do not replace R664.

Same-round Z3 has **115 verified / 124 raw** decisions. Its nine unconfirmed
results (eight UNSAT and one SAT) remain excluded. The existing input115 modular certificate was
rechecked against the identical input hash before counting that UNSAT for either
Xolver version; original measurements are preserved. This is a local improvement,
with a remaining 20-result verified gap to Z3. Neither protected set was evaluated.
An additional current-main server archive remains unnecessary.


## Rejected affine completion experiment (R671–R691, 2026-10-30)

The [closed experiment](AFFINE_COMPLETION_REJECTED_20261030.json) propagated exact
values entailed by the local affine context, minimized bipartite parameter
covers, supplied exact affine-slice candidates and connected the NIA client.
Its final R678 source passes 1,780 tests / 880,677 assertions, including exhaustive
small bipartite covers, signed/strict boundaries and independently replayed
integer and real witnesses. The parameter reductions on inputs77/149 are real,
but they do not establish a solver improvement.

The complete frozen comparison verifies **95 to 93**, with no new decisions and
two lost SATs: input150 (0.668 seconds to timeout) and input158 (0.066 seconds to
timeout). Verified PAR-2 worsens from 8154.269 to 8394.211 seconds. Same-round Z3
verifies 115 of 124 raw decisions; nine remain excluded. No opposite verdict or
invalid exported model occurs. Original invalid timing attempts for input7 and
the incomplete input10 run are preserved; complete same-budget three-solver
retries alone supply those two rows. R691 authenticates this distinction.

Diagnostics show that the new bounded search fails to reach complete original
models: input150 stops at depth14, while its prior search succeeds at depth27;
input158 uses fewer parameters but exhausts its allocation after 248 choices.
This is a candidate-search regression, not evidence of an incorrect SAT verdict.
The whole experiment is rejected and remains unmerged. Neither protected set
was read. Subsequent work starts independently from delivered main.

## Shared linear feasibility for nonlinear directions (R681)

`SubtropicalSatFinder` now reuses the existing exact `GeneralSimplex` through
frame choices, caching unconditional linear-row definitions and withdrawing
choice bounds at their levels. Local assignment preservation leaves the public
LRA/LIA backtracking policies unchanged. Parity contradictions reject frames
before linear feasibility. The private Fourier-Motzkin implementation is removed;
there is one linear backend, with no compatibility wrapper or new feature gate.

R681 passes 1,775 unit cases / 877,718 assertions, 12 focused subtropical cases,
63 parser checks, API examples and all four structural/evidence/ASP CLI checks.
A dense direction fixture changes from a 20-second component timeout to a
0.002220-second candidate, with independent original-model replay. On input155,
matching instrumented profiles show the nonlinear direction stage falling from
16.295 seconds to 0.040 seconds: one context, 146 definitions, 2,442 row reuses
and 158 linear checks. The direction search still finds no witness there; it
never turns this failure into UNSAT. These diagnostic results are excluded from
formal solver scores. Neither protected set has been evaluated.


The [qualified stage record](INCREMENTAL_SUBTROPICAL_STAGE_20261030.json) binds
source `9398d55d`, frozen CLI
`ac4c3142f19f2055fa35dd4f81ab9c61d56e136518bd9e9db81b9ff75a3474a2`, all
37 server acceptance groups, and R689/R695's complete original-hash audits.
The fixed160 round uses 60 seconds, one leased physical CPU and 16 GiB per
solver/case. The original input94 timing failure is preserved and excluded;
a complete same-budget three-solver retry supplies that row. No valid completed
attempt was replaced, and no source tuning occurred between pilot and remainder.

| Frozen version | Verified | SAT raw | UNSAT raw | Unknown | Timeout | Verified PAR-2 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Delivered main | 95 | 54 | 41 | 1 | 64 | 8146.500 |
| Incremental direction LP | 95 | 54 | 41 | 2 | 63 | 8142.884 |
| Z3 | 116 | 67 | 58 | 0 | 35 | 5541.432 |

There are no gained/lost verified decisions, opposite verdicts or invalid
exported models. Input155 changes from timeout to `unknown` in 47.643 seconds.
The 3.616-second aggregate PAR-2 difference is small; the demonstrated benefit
is the local direction-stage reduction, not closure of the verified solve gap.

Z3 has 125 raw decisions. R694 independently checks two supplementary SAT
witnesses on identical original hashes: input47 replays an existing exported
witness; input94 replays all 47,343 original ground Int/Bool interpretations,
which do not depend on 247 unused solver-private declarations. Every original
assertion is retained. CVC5 confirms both, in 0.667 and 2.672 seconds. Original
query/model timings and limitations remain recorded. Nine other results (eight
UNSAT and SAT122) remain unconfirmed and excluded. The remaining verified gap
is **21**, and neither a protected-set result nor an end-to-end QCP speed win
has been established. No extra current-main server archive is required.


## Delivery confirmation and next quadratic candidate (2026-10-30)

[PR69](https://github.com/fuqi-jia/Xolver/pull/69) merged as
`58ba6386dc1170a42f3f886da267ce5e5b1573bc` after both
[PR CI jobs](https://github.com/fuqi-jia/Xolver/actions/runs/40925328946) passed.
Its fresh [main push CI](https://github.com/fuqi-jia/Xolver/actions/runs/40928254309)
is fully green at that exact merge commit. The frozen R681/R689/R695 chain
remains its source/binary/evidence binding; no extra server archive is required.

The quadratic-sign implementation extends the shared refutation component
and wires its real and integer clients. For `a*x^2+b*x+c`, it proves nonnegativity
from explained `a>=0`, `c>=0` and `4*a*c-b^2>=0`; the constant-coefficient condition
is retained when `a=0`. Exact identities `p=q*h+r` combine known polynomial signs.
The prototype's zero-power quotient construction bug caused R696's reproduction
to decline, with no incorrect verdict; its failed native attempt is retained.
R697 fixes that construction, passes 1,780 tests / 877,774 assertions and all
three new real/integer/degenerate regressions, and independently confirms its
component UNSAT with Z3. Frozen CLI SHA-256:
`97f5b897ab377b9c029821584ed798666035cea30b240b6ca9894dc8bf64dc8f`.

Fresh R698's 16 development inputs gain input155: main returns `unknown` in
54.256 seconds, candidate returns independently confirmed UNSAT in 0.367 seconds.
There is no lost decision in that pilot. Matching diagnostics observe four
quadratic attempts, 17 divisions and one explained refutation in 1.802 milliseconds.
The complete fixed160 round and server acceptance are recorded below; this
pilot alone does not establish a whole-suite gain.
Neither protected set has been read.


## Explained quadratic sign refutation (R697/R700/R706)

The [qualified shared implementation](QUADRATIC_SIGN_REFUTATION_STAGE_20261030.json)
completes the real/integer closure. R697 binds source `4785fb46`, the frozen CLI
above, 1,780 unit cases / 877,774 assertions, 14 focused cases / 66 assertions,
63 parser checks and the real/integer/zero-leading regressions. R701 passes all
37 server acceptance groups, including QCP and independent model checks.

R703 audits all 160 unique original inputs and frozen versions. Every timed
row is valid, uses 60 seconds / one physical CPU / 16 GiB, and needs no retry.
Original UNSAT115 retains its independently rechecked original-input certificate.

| Frozen version | Verified | SAT raw | UNSAT raw | Unknown | Timeout | Verified PAR-2 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| PR69 main | 95 | 54 | 41 | 2 | 63 | 8143.809 |
| Quadratic signs | 96 | 54 | 42 | 1 | 63 | 8024.461 |
| Z3 | 116 | 67 | 58 | 0 | 35 | 5545.713 |

The sole change is independently confirmed UNSAT155: 54.256-second `unknown`
becomes 0.367-second UNSAT. No verified result is lost; no opposite verdict,
invalid exported model, crash or protocol failure occurs. This closes one
verified gap, leaving 20 in this same round, without establishing superiority.

R704 freshly confirms the existing input94 SAT witness with CVC5 on the identical
original hash. Input47 already has a valid standard replay from the pilot; an
unnecessary auxiliary lookup used the remainder path and failed before running a
solver. That failed lookup and the first rejected supplementary audit are
preserved. R706 uses only the required successful input94 evidence, changes no
timed observation, and excludes the remaining eight unconfirmed UNSATs and
unconfirmed SAT122. No valid timed row is replaced or rerun. Neither protected
set was read, and no end-to-end QCP speed win or extra current-main archive is
claimed or required.


## Rejected sparse tableau batching (R707/R709/R710/R718)

The [closed experiment](SPARSE_TABLEAU_BATCHING_REJECTED_20261030.json) replaces
per-coefficient pivot lookups with a reusable row-position index, with a direct
lookup path when a wide row changes in only a few columns. R709 passes 1,783 unit
cases / 1,315,472 assertions and 30 focused cases / 583,912 assertions. Three
paired component runs show about 2–6% faster common shapes and about 3.5% slower
wide sparse updates.

The fresh frozen 16-input comparison verifies **5 results for each version**,
with no gains, losses, opposite verdicts, invalid models or timing failures.
Verified PAR-2 changes from 1394.423 to 1391.620 seconds; the main linear gaps
remain timeouts. This does not justify expanding to another full160 round or
merging the experiment. Its code remains unmerged. R718 preserves the complete
timing, model, source and binary records; neither protected set was accessed.


## Consumer-directed active linear context (R717/R719/R722/R728)

The [qualified implementation](ACTIVE_LINEAR_CONTEXT_DEMAND_STAGE_20261030.json)
declares context consumption through the internal theory interface. NIRA
requests the current active linear constraints; checks without a consumer avoid
scanning and copying the registry. Each consuming check still receives one fresh
snapshot, including negated relations, with no snapshot retained across checks.
The explicit collection API and LRA/LIA backtracking policies are preserved.

R717 passes **1,782 unit cases / 877,805 assertions**, 63 parser tests and all
structural/API checks. R724 passes all **37 server acceptance groups**, including
QCP and independent model checks. In a 256-check passive component, SAT-assignment
reads fall from 262,144 to zero; its timing is not a whole-solver speed claim.

| Frozen version | Verified | SAT | UNSAT | Unknown | Timeout | Verified PAR-2 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| PR70 main | 96 | 54 | 42 | 1 | 63 | 8021.036 |
| Context demand | 96 | 54 | 42 | 1 | 63 | 8013.762 |
| Z3 | 116 | 67 raw | 58 raw | 0 | 35 | 5540.536 |

The complete fresh round has no verified gains or losses. SAT59 improves from
51.235 to 41.028 seconds with a checked model; the whole-suite PAR-2 change is
small and does not establish superiority. Eight Z3 UNSATs and SAT122 remain
unconfirmed and excluded. R730 freshly checks the existing input94 witness on
the identical original hash; timed observations and model-query limits remain.

Input58's first three timing observations overrun the budget and are retained
but excluded. R731 repeats the complete triad with identical frozen binaries and
60-second / one-physical-core / 16-GiB budgets; every valid original row remains
unchanged. Initial fixture/diagnostic failures and the successful source-chain
audit R728 are preserved. The export has since advanced to the separately
qualified sign-closure candidate; the frozen R717 binding needs no rebuild or
additional current-main archive. Neither protected set has been evaluated.


## Shared polynomial sign closure (R721/R723/R726/R733)

The [stage record](POLYNOMIAL_SIGN_CLOSURE_STAGE_20261030.json) binds source
`4edd86344fadd59c464bdaa4b4487ea94e4f5b4d`, the source-r721 overlay and every
frozen executable, native log, acceptance group and formal input hash.
The later merge of the context-demand documentation changes no qualified code.

The generic `search/refute/PolynomialSignClosure` pass is shared by NIA and NRA.
It propagates exact polynomial signs, derives common factors that must be
nonzero for a strict sum, cancels factors only under explained nonzero guards,
retains strict affine endpoints, substitutes exact fixed rationals and uses
identities `p = divisor*quotient + remainder` with constant-leading affine
divisors. A conflict includes its original SAT reason literals. All state is
local to a bounded invocation; exhaustion leaves the obligation open. Integer
and real clients use the same real-valid rules, preserving zero-factor cases.

On original fixed160 input37, the old path spends most post-portfolio samples
in CDCAC projection and subresultants. A nonzero-support chain now refutes all
three Boolean branches. The component takes 3.3–6.1ms per branch; independent
Z3 checks each returned reason subset as UNSAT. The actual original-file trace
records four sign conflicts taking 3.7–5.9ms. Whole-query time remains about
20.1s because the eager bounded SAT finder runs first; those diagnostic samples
are excluded from performance scores.

Panda1/ExperimentOS native qualification `ab83a5c7e2a0` passes **1,789 unit
cases / 879,143 assertions**, including seven new cases / 1,338 assertions,
96 generated exact rational SAT witnesses, six targeted SMT regressions,
63 parser cases, architecture/evidence/harness checks and API/parallel checks.
All **37** fresh whole-source acceptance groups in R727 pass. Compilation uses
the unique serialized build directory; acceptance verifies every manifest file
under a shared source lock.

Fresh formal R723/R726 compares frozen context-demand baseline and candidate
with the same Z3, rotating each case's versions on its one EOS physical CPU:
**60 seconds, 16GiB per solver**. R733 independently audits all 160 original
reports; there are no excluded timing rows or retries in this round.

| Frozen version | Verified | SAT | UNSAT | Unknown | Timeout | Verified PAR-2 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Context-demand baseline | 96 | 54 | 42 | 1 | 63 | 8005.205803 |
| Shared sign closure | **97** | 54 | 43 | 1 | 62 | **7902.244466** |
| Same-round Z3 | 117 / 125 raw | 67 | 58 | 0 | 35 | 5438.703380 |

The sole gained result is input37: baseline timeout, candidate **UNSAT20.124730s**,
independent Z3 UNSAT0.167907s. There are **zero lost solutions, opposite
verdicts, invalid exported models or protocol failures**. Input4 SAT moves
32.69→34.64s; input18 UNSAT47.29→44.05s; input59 SAT37.15→34.55s. The PAR-2
reduction is102.96s, principally the newly verified solution's removed penalty.

Original input115 remains checked by the exact modular certificate. Input94's
47,343 original ground integer/Boolean interpretations are freshly replayed in
cvc5 with all original assertions; unused model-private syntax is excluded only
after confirming selected values contain no such references. Same-round
input122's ordinary exported-model replay now succeeds independently, raising
Z3's verified score from the previous round's116 to117. The eight remaining
unconfirmed UNSATs (**12,24,27,42,50,80,114,159**) are excluded from verified
counts and receive the PAR-2 penalty. Timed observations are never replaced by
supplementary truth checks.

The frozen candidate CLI SHA-256 is
`db4293e9a72e054cf13c4ffdbb1491c45d1ddbd4e239e6d3d229a8f86bbdd931`;
baseline is`7f30dc0c8b55f53135a0a9c7a422ded45339db807e8ab2bfc940935389427973`.
This closes one real gap and does **not** establish superiority over Z3 or
whole-program QCP performance. Neither protected set has been inspected or run.
Server qualification, PR CI, merge and fresh main CI are complete; the current
continuation section links the exact delivery receipts. No extra current-main
server archive is required.

### Supplementary independent truth (R761/R770)

The [source-bound supplemental record](SUPPLEMENTARY_INDEPENDENT_TRUTH_20261030.json)
binds unchanged original input50
`7e71a151d917978f1b5afc2791abf589e30c8ff97e930979df6ef82ad72dcdc0`.
Independent cvc5 returns UNSAT in141.087235s with a300s offline verification
budget, one physical CPU and16GiB. This confirms Z3's original49.448217s timed
UNSAT; formal solver budgets remain60s and no timed row is replaced.
Z3's supplemented verified score is118/125raw, verified PAR-2 is5368.151597;
Xolver remains97 and7902.244466. The original R733 table remains unchanged.

Inputs12,24,27,80,114,159 time out in independent verification. Input42 hits
the separate ExperimentOS outer timeout without a completed checker record.
All seven remain unconfirmed and excluded. No opposite verdict is observed.
The initial audit used the wrong checker-output filename; its failure is
preserved and R770 rechecks the immutable evidence without rerunning solvers.
Neither protected set is used.


## Explained affine factor proofs (R782/R784/R785/R789)

The [frozen-stage record](EXPLAINED_AFFINE_FACTOR_STAGE_20261030.json) binds
qualified source `cb0ae6b51ef894365a8dc67dc57a726cd274c4e3`, its complete
cumulative overlay manifest, binary hashes and original timed reports.
Later receipt-only documentation changes do not change the qualified code.

On original public input127, real relaxations of all three active branches are
independently UNSAT, but the former closure exhausts its allocation on the last
branch. Backward sign propagation derives missing variable signs. Linear
resultants alone and variable indexing alone each give5→5 in their16-case
pilots. The final shared NIA/NRA implementation additionally proves strict signs
through nested exact affine decompositions of pending eliminants, rather than
materializing many irrelevant consequences first. Original SAT reason literals
support every consequence. Repeated zero factors are normalized using
`x^k*q=0 iff x*q=0` for`k>=1`, preserving zero roots. Each constant-leading pivot
is considered, fixed substitutions are reused locally and independent
consequences receive fair scheduling. All rules hold over reals and integers;
there is no input-name rule, runtime oracle, new gate or persistent branch cache.
The allocation remains10ms/100k-work/32rounds.

Panda1/ExperimentOS native `9574474e9823` passes **1,798 unit cases /
879,278 assertions**, including16 sign-closure cases /1,473 assertions,
96 generated exact rational SAT witnesses, eight targeted SMT regressions,
63 parser cases and the architecture, evidence, API and parallel checks.
All37 whole-source acceptance groups pass, including QCP regressions.
Eighteen original-premise unit conflict subsets are independently UNSAT in
both Z3 and cvc5. The actual last branch now closes in6.947ms and its selected
original premises are independently UNSAT in Z3. Component and profiler times
are excluded from formal scores.

Fresh R784/R785/R790 runs rotate all versions on each case's one EOS physical
CPU, with60s and16GiB per solver. R789 audit `bc3d081ca8eb` verifies all160
original hashes and observations. Initial triads10/78 hit the outer execution
limit; triad140 violates the wall-budget tolerance. They are retained as
invalid evidence, and only those three complete triads are freshly repeated
at identical budgets. All other157 valid original rows remain unchanged.

| Frozen version | Verified | SAT | UNSAT | Unknown | Timeout | Verified PAR-2 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Delivered main | 97 | 54 | 43 | 1 | 62 | 7935.750565 |
| Affine factor proofs | 98 | 54 | 44 | 1 | 61 | 7828.545163 |
| Same-round Z3 | 117 /125 raw | 67 | 58 | 0 | 35 | 5440.140412 |

The sole gain is original127: main timeout, candidate **UNSAT20.063328s**,
independent Z3 UNSAT0.331705s. There are **zero lost solutions, opposite
verdicts or invalid exported models**. Verified PAR-2 improves107.205403s.
Unknown remains1. The exact modular certificate115, independently replayed
original ground witness94 and supplementary300s independent UNSAT check50
establish truth only on identical input hashes; no timed row is replaced.

Seven UNSATs12,24,27,42,80,114,159 remain unconfirmed. This round additionally
leaves Z3 SAT32 unconfirmed because its model-producing query times out; no
previous replayed model was found. All eight receive the verified PAR-2 penalty.
Earlier118-verified Z3 figures belong to their own frozen rounds and must not
be substituted for this same-round score.

Frozen candidate CLI SHA-256 is
`9dfe72f19f1828fb44d03f46dcfe53800d6eeb25d7da8df2084ed7e2326b7baf`;
baseline is`db4293e9a72e054cf13c4ffdbb1491c45d1ddbd4e239e6d3d229a8f86bbdd931`.
The frozen diagnostic profile takes20.147s: all49 samples include the front
`EagerBitBlastSolver::solve`; four later polynomial sign conflicts take
2.525/2.995/7.088/2.961ms. This identifies a subsequent portfolio-scheduling
question, not another implementation or formal gain in this stage.

This closes one additional real gap and does **not** establish superiority over
Z3 or whole-program QCP performance. Neither protected set is inspected or run.
Server acceptance, PR CI, merge and fresh main CI are complete; the current
continuation section links the exact delivery receipts. No extra current-main
server archive is a delivery prerequisite.

## Native QCP trace capture and context feasibility (R792–R810)

The [source-bound native context stage](NATIVE_CONTEXT_SMT_STAGE_20261030.json)
binds qualified code `2364cd99`, native source manifest and binary hashes,
independent model witnesses and the original immutable observations.
[PR74](https://github.com/fuqi-jia/Xolver/pull/74) is delivered as main
`f1b7a194bad6db9402ee0f660a3078deeb9b3987`. Its qualified code
[CI](https://github.com/fuqi-jia/Xolver/actions/runs/41013084797), receipt-head
[CI](https://github.com/fuqi-jia/Xolver/actions/runs/41017751362) and fresh exact-head
[main CI](https://github.com/fuqi-jia/Xolver/actions/runs/41021331208) are fully green.
Receipt-only documentation changes do not change the qualified implementation.

The pinned native QCP binary exposes `QCP_DEBUG_SMT=1` diagnostics containing
printed Source/Target pairs and a result flag. The three unchanged public
development programs produce402 captured checks: branch106, GCD148, max3148.
The residual-only `--dump-smt-vc-file` output is not a complete query census.
R792 captures raw output, original C and binary hashes; R793, native EOS
`74498f9e716d`, exports all402 occurrences with no unsupported checks and passes
43 QCP Python tests plus architecture/regression-harness checks. The SMT CLI
remains byte-identical to qualified R782. `qcp_native.py` preserves applications
such as `Omod` and `Zgcd` as typed uninterpreted functions, without adding
unestablished arithmetic axioms. Native flags are observations, not evidence.

One observed `flag=-1` has a source containing `x<x` and target `True`.
Therefore that flag must not be labeled a refuted target: source infeasibility
and implication validity need separate checks. The generic SV `ContextSolver`
and `xolver-sv context` operation expose both, without changing ordinary
implication checking or assuming a QCP-specific flag ABI.

`Solver::decide` now connects a native assertion snapshot to the complete runtime
dispatcher. Standalone application fallback alone cannot dispatch all supported
array/UF combinations. Native import retains original DAG identity, rejects
ambiguous free-symbol names transactionally, replaces old query scopes, and
retains options and budgets. `dumpModel` enumerates original symbols for parsed,
native and programmatically constructed queries, including unconstrained symbols
known to the construction API; solver-introduced auxiliaries are excluded.
R802 native EOS`207d0d46fb15` passes **1,806 unit cases /879,437 assertions**,
including8 targeted cases /159 assertions, all67 parser/governance/evidence
checks and43 QCP Python tests. R806 freshly repeats the313-query existing QCP
corpus:291 UNSAT /22 SAT agree across CLI, SV and Z3, including203 replayed
interval certificates. R810 independently replays six native Int/Real/Bool/BV/
array/UF models through both Z3 and cvc5; cvc5 requires`--arrays-exp` for constant
array witnesses. Earlier compiler, harness and checker-configuration failures
remain recorded and are not substituted for these successful qualifications.

The402 captured occurrences contain95 distinct Source/Target pairs. R795 runs
their190 context/refutation formulas on the frozen native API, CLI, Z3 and cvc5,
on EOS physical CPUs with60s/16GiB per query. All760 observations agree: each
implementation has83 SAT /12 UNSAT contexts and5 SAT /90 UNSAT refutations.
There are no unknowns, timeouts, opposite verdicts or invalid models. R807/R808
audit352 SAT witnesses and408 independently agreed UNSAT observations. Eight raw
model records (four contexts through two Xolver entrypoints) omit unused UF
definitions. Only missing Int-valued functions absent from every assertion are
completed with the constant zero function; all original model bindings and
assertions remain unchanged, and **both** Z3 and cvc5 accept every completed
witness. Raw timed observations remain unchanged. Do not describe those eight
raw models as complete without this supplementary evidence.

The observed native flags correlate with344 feasible valid implications,
32 infeasible contexts and26 feasible non-entailments of the printed abstraction.
The last category does not refute a C program: printed functions remain
uninterpreted. Native flags are not used as correctness evidence.

R805 ABI control redirects four statically referenced calls to the actual
native implication checker **in process memory**, prints actual arguments with
the native FILE-based printer, and calls the unchanged live original checker.
All402 formulas and flags match R792 exactly; original binary and C/specification
hashes remain unchanged. This is a qualified interface prototype in local
validation evidence, not a shipped selected-backend replacement.

Capture and standalone replay do not replace QCP's opaque internal SMT backend,
establish complete native-call coverage, or verify a whole C program. A true
whole-program selected-backend comparison remains outstanding. Neither
protected set has been inspected or run. These binaries have no new fixed160
timing comparison; the preceding98/160 result belongs to its own frozen round.


The subsequent native ABI investigation establishes a different contract from
context feasibility: QCP's implication classifier first tests `S AND P`, then
`NOT (S IMPLIES P)`. It returns `-1` when the first is UNSAT, including a feasible
source with an always-false target; otherwise it returns `0` when the second is
UNSAT, and `1` when neither is refuted. The corpus correlation above is not a
universal ABI interpretation. The generic `ContextSolver` remains a separate
feasibility/implication API. Native replacement targets the lower single-formula
SAT entry, preserving QCP's own classifier and preprocessing.

## Selected native QCP SAT backend (R813–R820)

[PR75](https://github.com/fuqi-jia/Xolver/pull/75) implements actual native backend
selection, qualified code `9f36803e`; the source/binary hashes, EOS runs and
evidence boundaries are in the [stage receipt](NATIVE_QCP_BACKEND_STAGE_20261030.json).
Server acceptance and both exact-head [PR CI jobs](https://github.com/fuqi-jia/Xolver/actions/runs/41026885983)
passed. The PR is merged as main`b5a2fe6bd8895bec68af362fdf525410c26a1ddb`;
fresh exact-head [main CI](https://github.com/fuqi-jia/Xolver/actions/runs/41030001591)
is fully green. No extra server archive is a delivery prerequisite.

The pinned Linux QCP executable has no exported backend switch. The adapter
checks its full executable hash, native entry/call-site bytes and executable
device/inode, then replaces the lower SAT entry in memory. It serializes each
actual formula through QCP's FILE printer and runs only the selected frozen
Xolver or Z3. QCP retains preprocessing, branch classification and VC generation.
The original native solver is never a fallback. Unknown, timeout, unsupported
syntax and protocol errors stop the native invocation explicitly. The original
on-disk executable and C/specification hashes remain unchanged.

R815 runs the three original public development inputs through each selected
backend: **780 calls /402 branch diagnostics per backend**, 1,560 calls total.
All formulas, results and branch diagnostics match the live-original R813/R792
controls. Generated goal, auto and manual VC files are byte-identical.
Native mode0 does not occur on these inputs; separate native TT/FF tests cover
both modes with both backends. R818, EOS`1727e0789665`, qualifies final code,
49 QCP Python tests, architecture and the full regression harness, non-target
executable safety, explicit unknown handling and cancellation without a surviving
detached selected solver. Failure records are persisted before replies and
updated atomically so immediate native-parent exit cannot truncate them.

The 1,560 occurrences contain **174 distinct formulas:84 SAT /90 UNSAT**.
R817 uses up to64 independent EOS physical CPUs, one per task, with60s/16GiB
per solver invocation. All90 UNSAT formulas are independently UNSAT in cvc5.
For every SAT formula, both frozen Xolver and Z3 export raw models; all168 models
preserve the original assertions and replay SAT in both Z3 and cvc5:336 positive
replays, no model completions. R820, EOS`9f8370812cb1`, audits the exact queries,
raw witnesses, reconstructed replay assertions, positive checker outputs and
source-bound qualification. No opposite verdict or invalid model is observed.

This closes the native selection interface gap. The supplementary qualification
below completes the C→VC→selected SMT→Rocq path for one original development
program on both backends. It does not establish a program-suite coverage or timing
advantage. Xolver's core binary in this integration stage is unchanged from R802;
there is no new fixed160 score here. Neither protected set has been inspected or run.


R819/R821 additionally completes the original frozen `branch_destruct` C program
through actual native Xolver, external Xolver discharge and canonical Rocq
final-check: **1 verified program /10 original VCs /14 external queries**, all
external queries UNSAT and all candidate bodies identical to the checked full
VC proofs. Final-check EOS`578afc065663` returns`passed/done`; independent witness
and provenance audit EOS`ae37dfde9890` is backend-qualified, with no admitted
case proofs or extra assumptions. The complete controller workflow records564
native calls (222 SAT /342 UNSAT) across three frontend/freshness executions;
every actual formula hash/result matches the independently checked R817
inventory. Do not count repeated native calls as extra programs or VCs.
Original C/specification SHA remains`4d81aabd16ceb9d402fa0f1a3621dd8a6bf0ad28659bcb6cf60eedebec69e22d`.
The matched fresh Z3 workflow also passes canonical final-check, EOS`5bf4a7937bb3`,
with **1 verified program /10 original VCs /14 external queries /564 native calls**.
R824 pair audit, EOS`39db35282eaa`, authenticates both final checks, exact candidate
bodies and native query hashes/verdicts; all original VC token streams agree after
formal-module namespace normalization. The pair record SHA-256 is
`691b561a2ca19c138a272fa7912a7874af5735a2a21be4420b266bc7579b5d45`.
This is one unique program verified by each backend. The approximately33.8s final
controller timings are diagnostic, without matched CPU/order repetitions, and do
not establish a whole-program speed win.


## Shared explained Boolean/theory refutation (R823–R835)

[PR76](https://github.com/fuqi-jia/Xolver/pull/76) adds a theory-independent
Boolean refutation driver and a shared integer/real polynomial client. Exact
explained conflicts learn clauses before whole-formula SAT-only bit blasting.
An open or exhausted assignment preserves the original search allocation; it
never proves SAT. The conversion layer also rejects unsupported whole products
instead of accepting a converted prefix, bounds optional expansion work, and
rejects exponents outside the monomial representation.

The first minimal Boolean-support experiment R823 did not improve timing and
was not promoted. Complete true/false atom assignments in R825 close the
previously open branch. The fixed160 fresh round observes original37
(AProVE) **20.317s→0.0666s** and original127 (LassoRanker)
**20.067s→0.0671s**, with independent same-round Z3 UNSAT agreement.
The generic refutation stays bounded to8 Boolean models /1000 SAT conflicts
per solve /50ms; existing sign closure stays10ms /100k work /32 rounds.

Final Panda1/ExperimentOS validation passes **1,813 unit cases /879,499
assertions**, with38 additional source-bound regression/tool/model acceptance
groups. The MCSAT tests now directly connect parsed formulas, atomization and
real SAT/theory callbacks and require a positive backend check count; early
runtime proofs no longer make those backend tests vacuous. New API checks cover
assumption cores, SAT model validation and push/pop isolation. Independent signed
Boolean/polynomial checks cover56 integer/real cases:28 early refutations agree
with Z3 and cvc5, and28 SAT models pass56 positive independent replays.

The full fresh frozen160 comparison is **98 verified solutions before and after**
(54 SAT /44 UNSAT /1 unknown /61 timeouts), no gained or lost solves and no
opposite verdict or invalid exported model. Verified PAR-2 improves
**7822.034→7777.251**. Same-round Z3 is **117 verified /124 raw**, with seven
unconfirmed UNSAT results `[12,24,27,42,80,114,159]` excluded. R834 freshly
replays a prior raw122 SAT model in both independent checkers on the identical
original input hash; this supplements eligibility without replacing a timed
solve. Initial81/104 Z3 budget overruns are excluded; both original jobs and
children ended before all three versions were repeated at the unchanged budget.
The other158 valid original triads are immutable.

Qualified implementation/test head is`6e46e157`; frozen CLI SHA-256 is
`ce2c642efdb7a9b4e0f946ad6099a2f2f82f3a7b724f5e70caa4d1c59593f852`.
Final audit EOS`0732c961bbde` binds all sources, binaries, leases, acceptance and
witnesses in the [stage receipt](BOOLEAN_THEORY_REFUTATION_STAGE_20261030.json).
Both exact-head [PR CI jobs](https://github.com/fuqi-jia/Xolver/actions/runs/41038648758)
passed; PR76 is merged as`980969d35453c6138e5bfc351c90567859a7fd29`.
Fresh [main CI](https://github.com/fuqi-jia/Xolver/actions/runs/41041660875) is
fully green. This is a verified latency improvement, not overall superiority over Z3.
Both protected sets remain untouched. No extra current-main server archive is
required.


## Exact linear-fragment refutation (R846–R856)

Mixed NIA/NRA assignments can contain a contradictory linear subset. The old
complete linear stage required all active constraints to be linear and occurred
after SAT-only search. PR77 adds a shared exact Simplex relaxation before that
search: nonlinear rows and disequalities are omitted; original signed premises
explain every learned conflict. Strict bounds keep exact infinitesimals. Open or
exhausted relaxations never prove SAT. The local limit is2ms/100k work, clipped
to the existing50ms Boolean allocation; LIA/LRA backtracking policies are unchanged.

Fresh frozen fixed160,60s/one EOS physical CPU/16GiB per version, improves
**98→99 verified**:54 SAT/45 UNSAT/1 unknown/60 timeouts, gained1/lost0.
Original39 changes60s timeout→0.066s independently confirmed UNSAT.
Verified PAR-2 improves**7773.572→7659.084**. Same-round Z3 has**117 verified /
124 raw**, with seven unconfirmed UNSAT indices12/24/27/42/80/114/159 excluded.
R855 positively replays the prior raw47 model through Z3 and cvc5 on the
identical original hash; only eligibility is supplemented, never solve timing.
Four original budget/infrastructure-invalid triads51/72/86/94 are excluded and
repeated in full after their jobs end; the other156 valid triads are immutable.
No opposite verdict or invalid exported model is observed.

Panda1/ExperimentOS passes1,816 unit cases/879,519 assertions and38 other
regression/tool/model groups. Independent checks cover104 signed Boolean,
polynomial and linear integer/real cases:52 early UNSAT proofs agree with both
oracles;52 SAT models pass104 positive independent replays. Qualified code is
`372245e3`; frozen CLI SHA-256 is
`f27b1f2894090010d4937530c9538bd879fa442b463a98e8b3c817e4b4a7e0af`.
Final source/binary/lease/witness audit EOS`01b83557720a` passes; the
[stage receipt](LINEAR_FRAGMENT_REFUTATION_STAGE_20261030.json) binds the full
round and the exact PR/main CI links. PR77 is merged as`0f4acd1c`; fresh main CI
is fully green. This does not establish overall SMT or QCP superiority. Both
protected sets remain untouched; no additional server archive is required.

The next implementation generalizes the shared relaxation: each canonical
polynomial monomial is one unconstrained real column across all constraints.
The unchanged-budget private R854 diagnostic closes original113 in two Boolean
assignments/about4ms; independent Z3/cvc5 real relaxation checks agree UNSAT.
Unlike a successful relaxation proof, a feasible abstract model proves no
polynomial SAT result. The canonical module replaces the linear-only entry,
with no compatibility alias. This diagnostic is not a new formal score; the new
core requires its own build, correctness checks and frozen full-suite comparison.


## Shared polynomial linear relaxation (R857–R865)

The linear-only subset rule misses contradictions between nonlinear rows that
share monomials. PR78 gives every canonical monomial one unconstrained real
Simplex column across all rows. Every original model induces a relaxed model;
therefore exact relaxed UNSAT is sound for both integer and real clients. The
converse is not assumed: a feasible relaxation remains open. Strict bounds,
exact coefficients and original signed premise explanations are retained.
The canonical polynomial module replaces the linear-only entry without an alias.
The2ms/100k local and50ms global allocations and LIA/LRA state policies are unchanged.

Initial qualification is retained as failed. A full-target build reaches the
optional Python shared module and fails because the server's existing static
MPFR lacks suitable shared-object TLS. The established native-target list builds
successfully. The first rule order also increases an existing exact2-conflict
test to3: a weaker relaxed conflict precedes the direct sign contradiction.
Production now tries the cheap sign rule first; original strict assertions pass
unchanged. No test, search allocation or capability gate is weakened.

Panda1/ExperimentOS passes**1,817 unit cases/879,534 assertions**,38 other
regression/tool/model groups and22 targeted cases/154 assertions. Independent
signed Boolean/polynomial checks cover**152 integer/real cases**:76 early
UNSAT proofs agree with Z3/cvc5, and76 exported SAT models pass152 positive
independent replays. The fresh full frozen160 comparison is**99→100 verified**,
54 SAT/46 UNSAT/1 unknown/59 timeouts, gained1/lost0. Original113 changes
**60.017s timeout→0.0660s UNSAT**, agreeing with same-round Z3. Previous39/127
remain solved. Verified PAR-2 improves**7671.203→7549.853**; same-round Z3 is
**118 verified/125 raw**, verified PAR-2**5383.713**. Seven unconfirmed UNSAT
indices12/24/27/42/80/114/159 remain excluded. No opposite verdict, invalid
model, formal-budget violation or solver retry occurs in this round.

Qualified core is`62f19656`; frozen CLI SHA-256 is
`791960fb64631fe959933860938f9cfe101479098f5ccd40675ae290f784d69a`.
Audit EOS`75b6e7ad28a3` binds sources, native targets, original failures, all
160 timed triads, physical leases and unchanged-input supplementary truth.
The [stage receipt](POLYNOMIAL_LINEAR_REFUTATION_STAGE_20261030.json) records
full results. Receipt-only changes after the qualified core do not create a
new native solver version. PR78 is merged as`ecf1e7c6`; both final-head PR CI`41050990683`
and fresh main CI`41055517535` are fully green. Both protected sets remain unused.
The original GCD workflow below completes with this frozen core, and the
matched Z3 workflow also passes. Overall superiority remains unestablished. No
additional current-main server archive is required.


## Existing numeric predicate projection (R868–R873, candidate)

R870 diagnostic counters reject an unchanged-state propagation cache: original
48/51/131 complete4,344/1,479/2,505 propagation calls with0/0/1 repeated analysis
states. Propagation consumes about32.4/12.6/41.3s in these instrumented60s runs.
The first R869 observation omitted verbose output and collected no counters; it
is inconclusive and is not a benchmark result. No propagation result cache is introduced.

R872 identifies a different loss of information. Of1,877,665/233,327/427,474
attempted bound projections, only186,932/12,714/50,231 find an existing literal.
Original columns lack auxiliary-form metadata, and exact endpoint lookup drops
stronger facts such as`x<=2` when only`x<=3` is registered. These diagnostic
timings and counts are excluded from formal scores.

The candidate adds shared ordered projection onto existing linear predicates,
including both inequality polarities and equality points excluded by a proved
interval. LRA also maps original columns to single-variable forms and skips
already asserted conclusions. Queries never create atoms. Exact identity lookup
retains its distinct registration/introspection contract. New checks compare
rational half-line implication against all truth regions, including130-bit
endpoints, and exercise original-column propagation and backtracking. Exact
infinitesimal reconstruction and the existing LIA/LRA policies are unchanged.
R873 now qualifies frozen CLI SHA-256
`e151a159f220860e3579043ead7e8b121e9c497b652144316e87aff06df7ca9a`.
It passes36 targeted cases/79,402 assertions, all1,820 unit cases/883,125
assertions, LRA/LIA regressions,202 independent linear cases/102 models,
69 tool/parser tests and the QCP regression group. R874/R880 freshly compare all
ten remaining QF_LRA development gaps: both delivered main and candidate time
out on all ten. No wrong verdict or formal-budget violation occurs. This
standalone performance experiment has no added solve and is not merged; these
ten cases do not establish a full160 score or exclude regressions elsewhere.

The new-core original GCD workflow`native_gcd_xolver_r864-20261030194758` uses
frozen791960... throughout actual native calls. Annotation and independent VC
checking, all three groups, complete parent verification, final publication and
fresh final-check pass. EOS`a5c27eaaecde` returns `passed/done`; the entire
original C and frozen contracts remain unchanged. The independent R879 audit
authenticates1 program/9 complete original VCs and888 actual native calls across
generation/acceptance/final refresh:522 SAT/366 UNSAT over70 distinct formulas.
All formulas match prior independently checked truth. Failed intermediate Rocq
development checks remain recorded; they have no native SMT session and do not
replace the successful canonical checks. GCD identities use checked Rocq
mathematics, with0 post-generation external SMT discharge queries. The generic
audit's stricter external-discharge qualification remains false. See
[the functional receipt](GCD_NATIVE_PROGRAM_QUALIFICATION_20261030.json).
The matched Z3 run now also passes all groups, parent checking, publication and
fresh final-check (EOS`e903903352b9`, passed/done). R902 independently
authenticates both final checks, identical original goal token streams and all
888 native calls per backend, including each actual solver command and output
hash. Both backends verify1 original program/9 original VCs. Proof scripts and
development schedules differ, so final-check diagnostics are not a fair timing
comparison. No coverage or timing advantage is claimed. Both protected sets
remain untouched.


## Bounded linear propagation scheduling (R881–R882, candidate)

`LraSolver::stageCore -> LraPropagationEngine::propagateAll` previously seeded
every check from row0. The2,048-direction limit can inspect at most the first
1,024 rows before pending seeds, even on a tableau such as original51 with5,854
rows. R870 measures2,962,632 row visits across1,479 calls, near that limit.
Recomputing new states does not give the remaining rows a scheduling opportunity.

The unchanged R873 library reproduces starvation in R881:13 independent rows
have26 explained bound directions, but52 bounded calls discover only1. The
new candidate rotates the row/side seed across calls. Only the scheduling
position survives; values, explanations, snapshots and incident-row work remain
local, and every original budget is unchanged. New tests cover both iteration
and derived-bound limits, a different smaller tableau, strict rational bounds
and rollback. R882 qualifies core`b1a8c185`, CLI SHA-256
`4267fa39c09ea30e8e2402f32413f8e92e123645c2e29dde32c0927958037467`.
It passes38 targeted cases/80,173 assertions, all1,822 unit cases/883,896
assertions and the six initial regression/tool/model/QCP groups. R884/R887
cover the same ten LRA gaps. Original51 changes from timeout to42.952s SAT;
the other nine remain timeouts. Xolver's subsequent model attempts time out,
including the unchanged-input CLI model attempt R886, and remain recorded.

The unchanged aggregate verifier confirms the51 SAT decision with Z3's exported
model positively replayed in cvc5 on the identical input hash. This is1 correctly
decided pilot gain, not a checked Xolver model or a new full160 score. A per-solver
`verified=false` records missing local evidence; it must not be conflated with
absence of independently checked truth. An exported invalid model still fails
even if another solver establishes SAT.

R891 independently checks the existing native output flags for both Xolver
versions and Z3 on SAT/UNSAT fixtures, with positive independent SAT model replays.
The comparison harness now captures the model from the actual initial timed
decision for every solver. It no longer repeats a successful SAT search on a
rewritten model query. Model output remains within the common60s/16GiB budget;
independent replays remain separate checks. The aggregate rejects mixed model
capture protocols. A fresh full comparison must use the new protocol uniformly;
the old pilot timings are not substituted into that round.

R890 also rejects an all-assigned propagation shortcut: none of the measured
48/51/131 calls has every linear predicate assigned. No-output propagation costs
only about0.61/4.55/1.23s in those private runs, so that observation does not
justify a large general speedup. These diagnostics remain outside formal scores.

## Consumer-bounded linear propagation (R899–R900, candidate)

The uniform first-model round R894/R895 completes all160 valid frozen triads
without opposite verdicts, invalid exported models or protocol errors. The
rotating candidate gains original51 (60.019s timeout to36.639s SAT, with its
actual initial model positively replayed in Z3), but loses original59
(43.132s SAT to60.011s timeout). Both versions make100 raw decisions. Inline
independent evidence confirms99 each; original115 still needs its separately
checked modular certificate attached to this round. Inline verified PAR-2 is
7656.188 versus7655.901, effectively unchanged. This candidate has no net gain
and must not be merged on the pilot result alone. Z3 has124 raw decisions;
unconfirmed results and supplementary truth remain explicit rather than silently
counted. Original valid timings are immutable.

R899 links an observational LRA translation unit against the unchanged R882
core. R900 finishes three60s diagnostics with no opposite verdict. Its final
periodic sample for59 has484,804 derived bounds but only228,638 consumed before
the64-clause output limit;909 of1,169 calls hit that limit. For48 the counts
are1,995,473 derived/907,770 consumed. Instrumentation changes scheduling, so
neither these timings nor the diagnostic59 SAT is a formal improvement.

The new core streams explained bounds through the existing propagation entry.
The consumer can stop the scan when its output budget is full, avoiding the
unused suffix. The same exact local overlay, signed premises, mathematical
bound limit and circular scheduling remain; no callback or derived fact survives
the invocation. Batch collection remains a real use of the same API. Tests
check the exact batch prefix, reduced row arithmetic, subsequent resumption,
strict negative division and rollback. Native qualification and a fresh frozen
comparison are pending; no new solved count is claimed.

The first streaming build R901 passes40 targeted cases/80,270 assertions, all
1,824 unit cases/883,993 assertions and38 other acceptance groups. Its fresh
pilot restores59 (40.812s to18.311s SAT, both initial models positively replayed),
but51 times out. The complete160 round is still running; no net score is claimed.
Review also finds that streaming charged consumer latency against the existing
20ms producer budget, unlike the previous post-scan projection. The next change
accounts for consumer time separately while retaining the mathematical budget;
a slow-consumer regression checks that distinction. Qualification is pending.

R907 now qualifies that accounting fix:41 targeted cases/80,277 assertions,
all1,825 unit cases/884,000 assertions and38 other acceptance groups pass.
Its fresh pilot keeps59 solved (35.052s to17.558s SAT with positive initial-model
replays), but51 still times out. Full R909/R916 comparison is pending. The
preceding R903/R906 round has three invalid triads,130/131/154, with recorded
wall-budget overruns. They are excluded and repeated in full as R912; the157
valid triads remain immutable. A first stop audit opened the wrong EOS database
because its job working directory differed; it failed before finding or changing
a run. The corrected R915 audit asserts the canonical database and finds both
remaining jobs already terminal:0 jobs cancelled. No cancellation is invented.

## Unavailable linear extrema (R913–R914, candidate)

R913 observes the unchanged R907 propagation engine. In final periodic R914
samples, original51 builds1,469,082 row snapshots;1,162,211 have at least two
unavailable contributions for EACH extremum. Those snapshots consume8.146 of
10.456s snapshot arithmetic. Original131 spends24.484 of32.135s on such rows;
48 spends5.026 of13.562s. These instrumented diagnostics are excluded from
formal comparisons and show an additional cause beyond discarded output.

A forward bound needs every term; backward propagation can exclude only one
target term. Two unavailable terms in both extrema therefore preclude every
finite explained bound from that row. The candidate checks endpoint availability
before rational multiplication, addition and premise aggregation. The negative
snapshot is local and uses the existing input revision: newly derived non-basic
bounds requeue incident rows and invalidate it. No numerical fact survives a
call or rollback, and no arithmetic budget or solver gate changes. Tests cover
skipping all row arithmetic, strict negative division when just one extremum
becomes usable, rollback and a skipped row becoming productive during the same
local closure. Native qualification and frozen comparison remain pending.

The R908 completed audit now seals the preceding streaming core R901:
**100→100 verified**, no gained/lost result, PAR-2 **7539.698→7521.056**
(about0.25% better). Same-round Z3 has117 verified/124 raw decisions. The seven
unconfirmed UNSATs12/24/27/42/80/114/159 remain excluded. R905 confirms the
three duplicated initial Z3 models47/108/122: explicit`get-model` plus`-model`
printed identical model ASTs, positively replayed by both independent checkers.
Only truth eligibility is supplemented; no old solve timing is substituted.
See [the stage receipt](LINEAR_PROPAGATION_STAGE_20261031.json). The three
budget-invalid original triads are retained beside their valid full R912 retries.

R917 qualifies the unavailable-extrema implementation with43 targeted cases/
80,305 assertions. Its pilot is negative:48/51/131 remain timeouts, and59
regresses from39.109s SAT to timeout. No opposite verdict is observed. Saved
arithmetic changes the conclusions reached within the time allocation and the
subsequent search; the snapshot counters do not establish a solver improvement.
This candidate must not be merged on diagnostic arithmetic savings.

The next change addresses R900's observed duplicate conclusions:22,639 of
65,435 emitted59 clauses repeat a signed target, consuming the64-clause budget.
LRA now uses the existing predicate-acceptance filter to skip targets already
queued during this check, allowing another implied registered predicate to use
the slot. Original SAT assignments and signed premise explanations stay separate.
The set is local to the check; LIA's existing backtrack-epoch deduplication
policy is unchanged. A regression exercises two stronger row endpoints, two
weaker signed targets, exact clause replay over rational points, and renewed
emission after rollback. Qualification and a fresh comparison are pending.

Initial R921 qualification fails that new regression: after rollback the changed
row order can produce only one strongest endpoint, and the implementation still
extracts only one implied predicate from it. The two-target requirement remains
unchanged. Production now drains distinct existing targets from each endpoint
until none remains or the64-output budget is full. Exact original premises and
both signed targets are retained. The failed build is recorded; no binary was
frozen or benchmark score claimed for it. Requalification is pending.


## Qualified saturation of linear consequences (R926–R933)

The final core`f095b3b2` drains distinct existing predicates from each explained
endpoint, so one strongest endpoint can still propagate every applicable target
within64 slots. It retains exact rational/infinitesimal handling,512 derived
bounds,2,048 direction visits,20ms producer arithmetic and the existing LIA/LRA
state policies. No new atoms, solver gate, filename rule or external runtime
oracle is introduced. R921's failed two-target regression remains recorded;
production was fixed without weakening that requirement. A separate100-target
case checks the64-distinct-output cap.

Panda1/ExperimentOS passes**1,829 unit cases/897,855 assertions**,38 other
regression/tool/model groups and45 targeted cases/94,132 assertions. All54
Xolver SAT models from the actual timed solves positively replay. The fresh
full160 round verifies**100→100**,54 SAT/46 UNSAT/1 unknown/59 timeouts,
no gained/lost solve. Verified PAR-2 improves**7534.598→7498.860** (about0.47%).
Original59 improves**39.692s→2.823s SAT**, with its actual model checked; original
51/131 remain timeouts. No wrong verdict, invalid Xolver model, budget-invalid
triad or solver retry occurs in this round. Same-round Z3 is**116 verified/123
raw**, not the older125 raw reference; the target of at least126 verified
results is unchanged. Seven unconfirmed UNSATs12/24/27/42/80/114/159 are excluded.

R933 positively checks both duplicated current Z3 models47/108 with both
oracles. Its122 setup attempt fails before invoking a checker because all three
original timed solves return timeout; that valid timing is retained and no
original solve is repeated. Z3 model replays75/148 retain explicit error
boundaries; checked Xolver witnesses independently confirm those SAT decisions.
EOS`ea2b81d2d3b5` seals source/binaries, all160 leases and model/certificate
eligibility. See [the final stage receipt](LINEAR_PROPAGATION_SATURATION_STAGE_20261031.json).
CLI SHA-256 is`a5719bd76d2b443abe58de3e8bd80b8904c834cef1050f4574a087f11068555b`.
The stage is delivered through PR79 as main`51c0e641`; PR CI41099839678 and
fresh main CI41103752206 are fully green. Neither protected set was used.
This is a local propagation improvement, not overall superiority over Z3.

QCP R930 attributes20.477s of the historical GCD Xolver final-check to296
callbacks, versus12.605s for Z3; each has70 distinct inputs. Proof scripts and
schedules differ, so those totals are diagnostic. R931 runs all70 unchanged,
independently checked queries with both process orders: Xolver CLI starts total
2.357/2.531s, existing native worker batches0.421/0.422s; Z3 CLI2.725/2.752s,
reset batches0.516/0.567s. All decisions agree. Child CPU/system times confirm
startup cost. These are query diagnostics, not a C-program comparison. The next
QCP stage should connect a reusable task channel for both backends and repeat
canonical whole-program checking with matched proof routes and budgets.


## Persistent native task transport (R934–R937, program checks pending)

The canonical parallel worker now exchanges length-framed batches over one open
POSIX process channel. `WorkerSession` provides deadline-driven bounded I/O,
serialized requests, and process-group cleanup on timeout/protocol failure.
Spark reuses a session per partition. The old EOF-delimited worker transport is
removed; every client uses the same framing. Each SMT task still constructs a
fresh solver, so declarations and assertions cannot leak between tasks.

Native QCP uses this worker for Xolver and a persistent `z3 -in` process with
`reset` and checked response boundaries for Z3. Both execute every occurrence;
there is no answer cache. First startup, encoding and transport share each
60-second, one-physical-CPU,16-GiB query budget. Actual request/reply bytes,
process identity, query ordinals and process/query counts remain auditable.

Panda1/ExperimentOS passes1,831 unit cases/897,880 assertions,69 tool CTest
targets and the QCP regressions (including684 arithmetic equations). Focused
checks cover binary fragmentation, truncation/length errors, declaration/sort
isolation, task-error recovery, deadlines and descendant cleanup. CLI and SV
hashes are byte-identical to R926; the existing160-case score is retained rather
than replaced by another baseline run.

R935 replays all296 original GCD callback occurrences (70 independently checked
input hashes), including repeats. Every arm uses exactly one selected process
and returns174 SAT/122 UNSAT. In opposite execution orders, Xolver takes3.449/
3.290s and Z3 2.902/3.062s. Xolver remains slower in this diagnostic; it is not
an end-to-end C-program comparison. Canonical frozen-spec max3 runs have begun
for both backends, with owner/controller proof checking still in progress.
See [the transport receipt](QCP_PERSISTENT_TRANSPORT_STAGE_20261031.json).

R939 closes input on normal completion and requires exit0 with no unsolicited
reply bytes, so a failure after the last reply cannot be hidden by cancellation.
Timeout/error paths still kill and reap the process group. Seven transport
checks (including post-reply exit7 and trailing-output failures), seven QCP
adapter checks and all69 tool CTest targets pass again. All native/unit binary
hashes remain unchanged; the1831-case native result is retained. R935 timings
precede this shutdown fix and remain explicitly diagnostic. Subsequent whole-
program actions use the R939 source manifest, with the same frozen worker.


### Original max3 with both persistent backends (R937/R949/R952)

Both fresh runs now reach canonical`done` on the unchanged original max3.c
(SHA-256`7ddaa9f590cd9c37d3dd644ea280ecd3fa6cee084441c82caf9c0e1afb6dde5d`),
with all4 original VCs reconstructed and checked by Rocq. No specification,
assumption, helper or original obligation is weakened. R949 runs the two fresh
final-check actions sequentially on the same leased physical CPU0. Xolver takes
28.690s and Z3 29.536s. Each actual final refresh makes296 native SAT calls in
one selected process:148 SAT/148 UNSAT over60 distinct original queries, all
matching the independently model/judgment-checked R817/R820 inventory.

R952 authenticates every request/reply frame, query/formula hash, ordinal,
process identity, resource cap, complete controller state and original goal-token
stream. The whole program result is separate from the raw adapter's intentionally
false`program_verified` flag. External proof-discharge queries remain0: native
SMT selection is exercised during actual QCP symexec, while Rocq reconstruction
is common. Closers differ syntactically (`lia` versus `lia || int_auto`); one
program/order cannot establish an overall QCP performance advantage. Neither
protected set was used. This qualification binds frozen worker`578144c1` and
the delivered arithmetic core; a later core candidate needs its own evidence.
See the updated transport receipt. The broader multi-program comparison and the
fixed160 target of at least126 verified solves remain outstanding.


### Retain active children in iterative ITE traversal (R940–R956)

`NativeTerms::get` materializes a node by value. Phase two of
`IteLowerer::lowerAssertion` repeatedly decoded each wide parent and scanned its
completed children after returning from a descendant. On public fixed-suite
input13, R943 counted18,400,451 child scans for47,326 graph edges. A cursor-only
experiment reduced scans but still rebuilt the parent:4.303s→4.528s, so that
attempt was rejected. Owning the active child list as well as its cursor reduces
the same measured prefix to0.070s and scans each edge once. Root order,
postorder, generated constraints and incremental definitions are preserved.
The common frontend change applies across its supported theories.

R948 freezes source `d85eac56`, manifest SHA-256
`98d56c690144059be39ce9726797bd2bb4872267c66b10d271e2ea14214ebe6f`,
CLI `1906c863afad990600d3a6c017bc07396bc8fbe5ea1d62a589e0f1721267bd4b`,
SV `3748c3de132a04b77be700bc235867d6783004ed91fd3ba6bb718fff656c1fb9`,
and worker `67bfabc32e482637381e5e1cbbe4f272021695b8ead5363839de7588c1c3043a`.
R950 passes1832 unit cases/922470 assertions and38 other acceptance groups,
including the new4096-wide shared Boolean/Int/Real ITE regression and independent
model/arithmetic/QCP checks.

The full fresh160 comparison keeps60s/one leased physical CPU/16GiB and captures
models during the actual timed solve for all versions. R953 originals4/29/47
exceeded wall budgets under new external CPU contention; their failed records
are retained and excluded. All three became terminal before R954 reran each
complete triad once. The final valid selection has no protocol error, opposite
verdict or invalid exported model. Baseline verifies99 versus candidate100,
PAR-2 7588.984→7504.373; case4 changes timeout→30.935s SAT with its actual model
checked. No result is lost; matched cases18 and97 are slower by2.650s and2.111s.
Case13 remains a timeout: the diagnostic prefix speed is not a new solve.

Same-round Z3 has118 verified/125 raw decisions; unconfirmed UNSAT inputs
12/24/27/42/80/114/159 remain excluded. R955 independently replays the identical
duplicate original models for47/108/122 through both checkers; fresh certificate
115, existing input-hash-bound UNSAT50 and ground witness94 establish eligibility
only, with all measured budgets unchanged. Z3 model-format limitations75/148/94
remain explicit. R956 authenticates source, binaries, all39 acceptance groups,
all selected timing/lease/model records and the negative/positive traversal
diagnostics; receipt SHA-256
`de78d8330fc7ed68f6882e215b6d89df8c0671fe62d043fd5f026975f8c9027b`.
The earlier delivered round already reached100; no historical coverage increase
or superiority over Z3 is claimed. Neither protected set was used. The original
max3 qualification above belongs to the preceding frozen worker, not this
candidate's full-program performance. See the ITE receipt for delivery status.


### Deferred row explanation merging rejected (R957–R963)

Existing stack samples placed11/25 frames for public LRA gap131 in propagation
and10/25 in simplex pivots. Private counters counted1,957,664 premise-map updates
for226,069 improving candidates in a ten-second diagnostic. Prototype642a4f9e
therefore deferred each immutable row snapshot's explanation union until a
numeric endpoint improved. It passed50 targeted cases/34846 assertions, including
shared excluded premises and unchanged-bound rows.

The fresh six-case pilot rejected the change: baseline3 verified versus
candidate2, PAR-2 426.113→516.275, no gains and one loss at51 (30.384s SAT with
its original exported model checked, versus candidate60s timeout). Every triad
has a valid lease/budget, no opposite verdict and no invalid model. R963 seals
all records (SHA-256
`61e90552e23caea3e65df0da0f853373bfb15e0f2c2aea351a6ac6a8731ca540`).
The implementation, added counters and prototype tests are removed; no full160
expansion or valid-trial rerun is justified. No protected input was used.

R960 separately exposed a Python test observation race: init reaped a killed
orphan between `/proc` existence checking and reading. Commitcaeea3b7 reads its
state once per observation and accepts an already reaped child. R962 passes all
50 native targeted cases, seven transport tests, seven QCP adapter tests and
three architecture/parallel CTests, with every native byte unchanged from R960.
This test-only fix remains in PR80; its new exact-head CI is41121158561. The
prior failed run and the completed requalification remain visible. See the
[closed experiment receipt](DEFERRED_ROW_EXPLANATIONS_REJECTED_20261031.json).


### Difference-logic constant identity and model repair (R964–R974)

A user variable named`__ZERO__` collided with graph node0, while getModel
silently omitted any user name beginning`__`. Fresh constructed IDL/RDL inputs
`(assert (or (= __ZERO__ 1) (= __ZERO__ 2)))` produced two wrong UNSAT answers;
both independent solvers returned SAT. Two analogous`__user` inputs returned
SAT without an available model. R964's diagnostic stopped on that unavailable-
model parser error; the complete R965 report retains all six inputs and two
ordinary-name controls (SHA-256
`a294e510967f542cd9d8d034b260f61a77f962df98815d3380a35b21d592f732`).

Commit`d5a3d306176e39b74f1ac6035e992a6879c9d6f2` separates the constant vertex
from the symbol map in both batch and incremental graphs, uses explicit absent
endpoints for zero in both solvers and their shared disequality splitter, and
exports user names without a prefix filter. No old name alias remains. Tests
cover both weights, graph backtracking, positive/negative bounds, model invalidation
and the exact unary split tautologies. R966 passes68 targeted cases/284883
assertions and20 IDL/17 RDL regressions; source manifest SHA-256
`5632802701cb5789dc8f16dedeb66b7a2924b4faa85979fb9ab61ae67fd021b2`,
CLI`9d11c22d874ac89acd45785c6a5b3920d9bdbfe2dcf1ece64cf227113ef4b368`.
R967 authenticates six matching input hashes and positive replay of every actual
exported model through both Z3 and cvc5 (report SHA-256
`e7ae7a0273fd1212d43fe7c79a99b21b6490750bdce521501503acad1b365517`).
These are correctness/capability regressions, not additional fixed160 solves.

All39 R968 acceptance groups pass, including1837 unit cases/922772 assertions.
The completed fresh R969/R971 fixed160 round keeps60s/one physical CPU/16GiB
and initial model capture. Both Xolver arms verify100 (54 SAT/46 UNSAT), with
59 timeouts and one unknown; there are no gains or losses. Verified PAR-2 is
7506.071 baseline versus7513.404 candidate. Same-round Z3 verifies117/124 raw;
seven unconfirmed UNSAT inputs12/24/27/42/80/114/159 remain excluded. There
are no protocol errors, opposite verdicts or invalid exported models. R972
positively replays the actual timed duplicate models47/108/122 through both
independent checkers. R974 seals source/binaries, all39 acceptance groups,
all160 original timing/lease/model records and the six distinct correctness
diagnostics (SHA-256 `c7812033037fed492e7e70cdc88b9606bed08b5b2296699c1d16d69ff3e9a667`).
R973 failed only because its audit misclassified the old diagnostic label
`model_replay` as Xolver rather than Z3; its original command proves the Z3
checker. That failed audit remains retained, and no solver run was repeated.
The correctness repair is retained; no overall speedup is claimed. No protected
set was used.
See the [symbol identity receipt](DIFFERENCE_LOGIC_SYMBOL_IDENTITY_STAGE_20261031.json).

The persistent transport stage is merged by PR80 as main
`ec1912f519cba5455155725adb6ab829d0a357eb`, after exact-head
[PR CI](https://github.com/fuqi-jia/Xolver/actions/runs/41121158561) passed.
Its fresh [main CI](https://github.com/fuqi-jia/Xolver/actions/runs/41124740311)
has completed successfully. The CLI/SV bytes of that transport-only
stage are unchanged from R926. PR81 subsequently merged the owned-child ITE
traversal and difference-logic identity repair as main `795fb15a1d81514c61f9369f438d5c3914593a18`,
after every step of exact-head [PR CI](https://github.com/fuqi-jia/Xolver/actions/runs/41129059624)
passed. Its fresh [main CI](https://github.com/fuqi-jia/Xolver/actions/runs/41132389466)
is currently running. The subsequent indexed-context kernel below remains separate.


### Shared source-indexed incremental context (R976–R987)

Private counters on three public LRA inputs found repeated linear lookups of
already retained SAT sources. The final periodic snapshot for51 within a ten-
second diagnostic has276782 calls/1115918214 comparisons, zero replacements,
and739682185ns in the instrumented scan. Inputs48 and131 likewise have zero
replacements after169855546 and86632324 comparisons. These instrumented costs
are diagnostic evidence, not formal solver timings.

Commit `2d3d1de90f1faddc5f67e6e029176a42cb9e0e62` adds a reusable indexed
incremental context, adopts it in LRA/LIA/the common arithmetic base, and removes
the separate manual LIA index. The key projection is independent of SAT or theory.
The index follows replacement, duplicate first-source lookup, prefix withdrawal,
filtered backtracking, snapshots and reset. Append-only clients build no index.
LRA keeps suffix withdrawal/preserved assignments; LIA keeps filtered withdrawal,
source order, snapshots and its established assignment policy.

R978 freezes source manifest SHA-256
`03920335ad30631eb68f709948dcc3213c5171a5c1f5954c08f4c68373f47f46`,
CLI `4d459fa5acfcf9c95d31bc7117d14701156f411439139904b1d58e00ffd1aec3`,
SV `b428d0dda5a6f7662820f824b68da6d49b2dd9374c3913cbf079f00a309d6334`,
and worker `47f18f753da840b14cb48ca9e9e61be6a4943a48741435ddb0ec6b4fc3208fc8`.
196 targeted cases/369578 assertions and all39 full acceptance groups pass,
including1840 unit cases/969357 assertions and independent arithmetic/model/QCP
regressions. Random source operations check replacements, duplicates, filtering,
snapshots and prefix withdrawal against an independent vector reference.

The pilot verifies10/16 in each Xolver arm, PAR-2 902.921→900.530, with no gain
or loss. R983 authenticates it before the144 disjoint R984 inputs run once.
The full fresh round keeps60s/one physical CPU/16GiB and initial-model capture:
baseline9d11 verifies100, candidate4d459 verifies100, PAR-2 7519.626→7516.225.
There are no gained/lost solves, opposite verdicts, invalid models, protocol
errors or retried originals. The small3.401s (about0.045%) PAR-2 difference does
not establish a material/statistically significant overall speedup. Same-round
Z3 verifies118/125 raw; the seven unconfirmed UNSATs remain excluded. R987 checks
the actual timed duplicate models47/108/122 through both independent checkers.
R986 seals source, all binaries/logs,39 acceptance groups,160 original timing/
lease/model records and the private lookup profiles (SHA-256
`0e8d7ad96e7807a8c6e360f8a322c339581cf5681036ee36102b17bde7d759c7`).
Neither protected set was used. No new whole-program QCP claim is made. See the
[indexed-context receipt](INDEXED_INCREMENTAL_CONTEXT_STAGE_20261031.json).

### Bounded exploratory diagnostics after the indexed stage

R970/R975 change only the declared header on public gaps13/131: existing IDL/RDL
returns unknown. Their actual lowered constraints include ternary sums, so pure
fragment dispatch is not justified. A read-only structural scan finds413 distinct
non-DL forms in131 covered by four numeric parameters. R980 exhausts the16
0/1 assignments on restricted derived-header subproblems:15 UNSAT and one10s
timeout, no verified witness. Restricted UNSATs do not refute the original input;
no production dispatch or fixed160 gain follows.

R985 profiles three public NRA gaps with the frozen indexed CLI,10s each.
Input69 calls linear relaxation175 times for6729.1ms; stack samples place14/24
in computeSimplexTableauFacts and6/24 in GeneralSimplex::addConstraint. The
current call path reconstructs monomial columns and the tableau at every check.
A persistent exact relaxation shared across polynomial clients is the next
candidate; no implementation or gain is claimed yet.

For77/149,23/24 samples lie in square-cascade substitution; the implementation
rebuilds coefficients even when a substituted variable is absent. R988 compiles
a private prototype using existing RationalPolynomial::substitute and skipping
absent variables, without changing production source/library/CLI/unit bytes.
R989 still times out after10s on both inputs;77 reaches the next stage after
6.801s in square-cascade,149 does not. There is no verified new witness or formal
score change. This exploratory prototype is not promoted on that evidence.


### Incremental monomial relaxation: qualified, no pilot gain

Commits85a6e063/f97e63bd replace repeated relaxation reconstruction with a
persistent PolynomialLinearRefuter shared by NRA and polynomial Boolean
refutation. Reused auxiliary rows retain no asserted bounds; every check
replaces the complete current explained bound set and validates conflict
premise membership. Cache identity compares full polynomial contents. Reset,
withdrawal, polarity changes, changed polynomials and constant disequalities
are covered, including160 branch contexts against a fresh independent tableau.
R990 freezes CLI1bd8aa16 and matching SV/worker; R993 passes all39 server groups,
including1844 unit cases/969857 assertions. R991 runs16 fresh original-input
triads at60s/one leased physical CPU/16GiB: both Xolver arms verify7, with no
new or lost solves and PAR-2 difference below1ms. Z3 verifies12/14 raw;
unconfirmed UNSAT24/27 stay excluded. R994 seals all source/binary/acceptance/
model/lease evidence (SHA-25610d72b7be8a64fff2340c2ffc72b61d7498ec220f78f0cccb6a0c5bc2f82141e).
This standalone version is not promoted; no full160 expansion, protected-set
run or whole-program QCP claim follows. See the
[bounded pilot receipt](INCREMENTAL_MONOMIAL_RELAXATION_PILOT_20261031.json).

R995 privately observes exact stage inputs and univariate operation counts,
without modifying production source or binaries; R996 profiles public69/77/149
for10s each. None of the observed presolve/box inputs equals its predecessor.
On69, one UnivariatePolySignAnalyzer run visits1163 univariate atoms, performs
2773755 full-input cut scans and takes377982us. The atom count is2385; later
runs grow with the assignment. Rational roots do not consume those cuts at all.
The next core candidate builds a variable-indexed rational-cut table lazily,
once per sweep, only when an algebraic root actually needs refinement. This
shared PresolveEngine capability serves NIA/NIRA/NRA. It retains exact rational
endpoints, current-domain cuts, root refinement and original reason semantics;
new tests mix rational/irrational roots and independent variable bounds. Native
qualification and solver-level benefits remain unproven for that candidate.

PR81's exact-merge main CI41132389466 has passed both jobs and every step.
PR82 is merged as48054c2d after PR CI41133766183 passed both jobs and every step;
its exact-merge main CI41136383267 is currently running. No extra server archive
is a delivery prerequisite.


### Indexed rational cuts: qualified pilot, no solver gain

Commit63ba37b5 is frozen by R997 as CLI95b84a04, SV1c0099cb and
workere1e3ea6c. All39 R999 server acceptance groups pass, including1846 unit
cases/969873 assertions; targeted53/1432 and NRA231/NIA134/LIA80/LRA61 pass.
R998's16 fresh original-input triads verify7 for each Xolver arm, no gained/lost
solves, invalid models, opposite verdicts or protocol errors. PAR-2 is1081.768
versus1081.769; same-round Z3 verifies12/14 raw, with unconfirmed UNSAT24/27
excluded. R1001 seals source, logs, binaries, leases and model checks (SHA-256
`a8dc06076b5c89f7c840b19de59ea142039a691f02f1e403e06bb754b01ed0f4`).
This standalone candidate is not promoted or expanded to full160. Neither
protected set was used. See the
[cut-index pilot receipt](INDEXED_RATIONAL_CUTS_PILOT_20261031.json).

R1000's public profiles show why the local improvement does not suffice: on69,
presolve can now enter PolynomialEqualityCombination;12/24 samples land there,
and individual presolve calls take about1.1s despite the existing50ms allocation.
Its dense transpose includes zero columns for every affine equality and forms
all null vectors before publishing any consequence. The follow-up replaces that
matrix with sparse exact elimination of nonlinear monomials, retaining exact
source coefficients (and removing canceled premises). Completed affine facts
are published incrementally; partial work is local and observes the existing
presolve/global deadlines. Affine inputs are retained, rather than recombined.
Tests compare resulting consequence spans and reason-restricted membership with
an independent dense solver on80 satisfiable integer/real rational-coefficient
systems, plus expired/resumed work and a256-affine-premise control. This next
source candidate still requires native qualification and a fresh fair pilot.


### Sparse cancellation and interval projection pilots: no solve gain

R1002 qualifies commitc921c75c as CLI9648db59, SV3af543ac and workeraca97b72.
Targeted56 cases/4494 assertions, NRA231/NIA134/LIA80/LRA61 and all39 R1005
acceptance groups pass, including1849 unit cases/972935 assertions. R1003's16
fresh original triads still verify7 for each Xolver arm; no gained/lost solves,
opposite verdicts, invalid models or protocol errors. PAR-2 is1081.720 versus
1081.774; Z3 verifies12/14 raw, unconfirmed UNSAT24/27 excluded. R1006 seals the
source, binaries, complete acceptance and timing/model/lease records (SHA-256
`0a58168460fa14f9b975ae41dc614621847804c6c2dcfb99b3b517b5892667c5`).
The standalone sparse stage is not promoted or expanded to full160; see the
[sparse pilot receipt](SPARSE_POLYNOMIAL_ELIMINATION_PILOT_20261031.json).

R1004 public69 records presolve at59–61ms/call, versus about1.1s after the cut
index alone; pipeline snapshots increase from11 to56 calls in the10s window.
The remaining box contraction costs about290ms/call. R1007 privately caches
immutable degree-one/two projections only for incident unassigned variables,
retaining original constraint/variable/round order and the noContract proof
path. The initial unit link fails solely because the experimental script omits
LIBRARY_PATH for native GMP. R1009 completes that link and99 component cases/
287 assertions, reusing the already compiled object and CLI without rerunning
successful work; original source/CLI/archive/unit bytes are unchanged.
R1008 lowers69's observed box calls to130–140ms, but all three10s diagnostics
still time out. R1010 tests eight fresh original-input triads (22/65/69/72/77/
144/146/149),60s/one physical CPU/16GiB: both Xolver arms verify2 and time out6;
Z3 verifies7, with no unconfirmed result. There are no gains, losses or errors.
R1011 seals these records (SHA-256
`1aeebefa1a034b290c0aa605343fd098e712a5e4690740a335210189f98ac002`).
This private projection-cache experiment is not promoted; its99 checks do not
stand in for a full production acceptance. See the
[projection-cache receipt](BOX_PROJECTION_CACHE_PILOT_20261031.json).

R1012 is a new private bounded-state experiment: two owned source-and-domain
frames, reused only after exact full polynomial/relation/reason prefix checks.
A retained ancestor box is valid under still-active premises; changed prefixes
start fresh. It records source-prefix hits. Private thread-local ownership is
not a production API: promotion requires solver-instance ownership, reset and
withdrawal tests. No result or score is yet claimed for that experiment.
The existing IcpEngineQ has a watcher worklist but its ReasonedBoxQ/IntervalQ
contract requires finite initial domains; do not invent finite bounds or wire
an empty box as the whole real line. These components are not currently called
from production solving despite retained includes.

PR82's exact-merge main CI41136383267 has passed both jobs and every step.
Neither protected set was read or run. The current full160 reference remains
R986's100 verified Xolver versus118 verified/125 raw same-round Z3. No new
whole-program QCP result belongs to these kernels.


### Candidate scheduling pilot and projected-point follow-up

R1012's private prefix reuse passes99 cases/287 assertions. R1013 confirms
exact prefix hits (e.g.2391 retained sources and1217 domain variables on69),
but box calls remain about150ms and all three10s diagnostics time out. This
isolated state-reuse prototype is not promoted; no production thread-local
state was added. The next scheduling experiment returns to the qualified sparse
parent, without either private interval-cache prototype.

R1014 moves whole-input presolve/box stages to the existing CandidateModel
schedule and passes165 cases/9065 assertions. R1015 public69 reaches a full
candidate after441 linear-relaxation calls; its boundary search exhausts20ms
in preparation (1217 variables,252 retained equality unknowns,0 contexts/checks/
models). Other public profiles still reach square-cascade and time out. R1016's
eight fresh formal triads verify2 for both Xolver arms and7 for Z3, no gains,
losses, errors or unconfirmed verdicts. R1017b seals this and the prefix experiment
(SHA-256`7d77b3bfd8b0e7626352c028d4bed4f1f92208acdfb9f800c3a2fc0ac756577c`).
The original R1017 audit fails only because it expected a source-manifest field
absent from the private qualification schema; the repair verifies the exact
original-source hash/transformation, native outputs and parent manifest. No
successful solver/test/timing run is repeated. See the
[scheduling receipt](NRA_CANDIDATE_SCHEDULING_PILOT_20261031.json).

The new core follow-up projects the existing monomial-relaxation assignment
onto original variables, preserving exact infinitesimals and completing
variables without degree-one columns with zero. The shared projection API
explicitly returns an untrusted point. NRA tries it only at full effort, outside
interface-combination mode, and accepts it only after checking every original
polynomial/interface constraint exactly. Projection can therefore reuse a point
after an inconclusive relaxation without inferring SAT from relaxation
feasibility. Other stages remain available on rejection. Tests cover a2^-256
open interval, current-source withdrawal, exhausted work and a feasible
relaxation whose projection violates x²=2. Two new NRA regressions cover exact
open bounds and rejection of a non-original model. The stage schedule is an
unqualified dependency of this new combined candidate; none of these changes
has a new verified fixed160 gain or whole-program QCP claim yet. Next: native
source qualification, constructed-model replay, full acceptance and fresh pilot.


### Projected relaxation candidate: complete negative pilot

R1018 qualifies sourcee02dd31d (manifest SHA-256
`bf04b005fb43ca9eebab321629917561f9828e027f39b1bd323c7b27a1afe0e4`),
CLIef801757, SV798c913c and worker2dca37d8.58 targeted cases/4510 assertions,
NRA233/NIA134/LIA80/LRA61 and all39 R1021 acceptance groups pass, including1851
unit cases/972951 assertions. The2^-256 open-bound SAT witness is replayed
independently; the non-original relaxation assignment case is independently
UNSAT. The long4-variable modular unit case takes120.030s on both the prior
sparse unit run and this run; it is not a new hang/regression.

R1019's12 fresh original-input triads (20/22/65/69/70/72/73/77/144/146/148/149)
retain60s/one leased physical CPU/16GiB and initial-model capture. Both Xolver
arms verify6 (4 SAT,2 UNSAT) and time out6, with no gains/losses/errors or
unconfirmed verdicts. PAR-2 is721.599 versus721.653; Z3 verifies11, PAR-2 159.561.
Every actual Xolver SAT model replays positively. Z3's148 root-object replay
boundary remains explicit; independently verified Xolver witnesses establish
input truth. No valid trial is repeated. R1022 seals source, binaries, all39
acceptance groups, constructed diagnostics and original timing/model/lease
records (SHA-256
`60de05a7afbb0e5e9ab142d3584788a29842c452a5b8876013db3a07f66943cf`).
This combined candidate is not promoted or expanded to full160; see the
[projection receipt](PROJECTED_RELAXATION_CANDIDATE_PILOT_20261031.json).

R1020 rejects the projected point on all three public gaps:69 has1217 variables
and spends6890us on projection/validation;77 has132/940us,149 has135/1372us.
All three10s diagnostics still time out. On69, the existing boundary search
still expires during parameter preparation without building a linear context;
on77/149 it reaches only37/66 of80/70 parameters before its20ms allocation,
then square-cascade dominates. There is no validated new model from the point
projection alone. The next investigation should measure candidate repair from
the existing LP point versus the current local-search start, or eliminate
repeated full rescoring in the greedy monomial cover. Keep exact original
validation, scoped state and the fair final suite. Do not repeat the closed
interval-cache, prefix-value-only or standalone projection experiments.

No new PR is open for these zero-gain candidates, and main remains48054c2d with
fully green CI41136383267. The development branch retains the qualified native
commits and bounded receipts; Draco is unchanged. Both protected sets and the
fresh multi-program QCP comparison remain outstanding. The main fixed160
reference is still100 verified Xolver versus118 verified/125 raw Z3, not a win.


### Indexed candidate preparation and the remaining branch-explanation gap

Core624af3d1 replaces repeated full monomial rescoring with an incident-edge
weighted greedy cover, preserving the entire score/tie order. The helper accepts
ordered node types and integral weights without arithmetic-theory dependencies.
Parameter-to-atom indexing also follows actual support instead of every parameter.
An independent full-rescan reference, weighted/retained/overflow/cancellation
cases and a2000-edge work-allocation test pass. R1023 native qualification and all39
R1026 groups pass,1856 cases/978660 assertions. R1025's12 fresh60s/one physical
CPU/16GiB triads still verify6 for each Xolver and11 for Z3: no new/lost solve,
error or unconfirmed input. PAR-2 is721.603/721.604. R1027 seals this negative
pilot (`7d96f5d797fc0c42a41fe7703d1687f9d722e3883e372e4edd0f87299c064c4f`).

R1028/R1029 and R1030/R1031 separately test LP-seeded rational repair and
LP-seeded affine prefix completion; each private native binary passes182 cases/
14928 assertions without changing production source, CLI, archive or unit bytes.
All six20s public profiles time out. The LP point does improve exact false-atom
counts versus prepared starts:476→134,36→34,24→11 on69/77/149. On69, however,
initialization consumes about2.086s of a250ms local allocation before the walk.
The seed transport is private scaffolding, never a production thread-local API.
R1032 seals both prototypes and freezes an old-header/old-library initialization
harness before the next overlay
(`b22bbd2a96181a40a65e1d26954bae6290cfdb1819d8ee9af3fe337dc8f21fc2`).

Core469baa27 indexes unary bound sources in one pass instead of variable×source
rescans. Initialization SAT probes stop at the first violated atom instead of
computing a complete normalized score. Source/variable order and the first
combined midpoint stay unchanged. Bracket extraction and probe loops now check
the existing local/global deadline; cheap statistics reset on every call.
A200-variable coupled test checks exact witnesses, scan/probe counts, reversed
variable order and repeated calls. R1033 qualifies manifest SHA-256
`adbc83fe9fc6771133b2eec7bda558c9cc4184fd77230405dc7cc848eb5feaa7`,
CLI638941b7, SVe398e33f, worker0935ff15;98 targeted cases/15610 assertions pass.
All39 R1036 groups pass, including1857 unit cases/979070 assertions.

R1038 compares identical harness source linked to frozen old/new native
libraries, alternating order on the same leased physical CPU,60s/16GiB per arm.
Both use a250ms local allocation and zero walking rounds. On constructed200-
variable bounds plus a coupled product, initialization is102195→4515μs; on1217
variables,4387397→28636μs. Every actual complete model replays SAT with both Z3
and cvc5. This is an initialization-only result from two constructed inputs,
not a Z3 timing comparison, fixed160 gain or whole-program QCP claim.
R1034's12 fresh original-input triads still verify6 for both Xolver arms and11
for Z3, PAR-2 721.600/721.652/159.215, no gains/losses/errors/unconfirmed inputs.
Actual Xolver SAT witnesses all replay; the explicit Z3 root-object model
boundary on148 remains. R1037 seals qualification, full acceptance, fair trials,
profiles and these model checks
(`537be04f6fca9bf2ff6ee491352732be38e2209435a59c5e590c4ea1b931cce0`).

R1039/R1040 tests the LP-seeded prefix method with a separate one-second/
one-million-work allocation on qualified469baa27. It does not change production
budgets. All three20s profiles still time out:69 reaches50/167 parameters with
8311 choices;77 remains37/80 after33366 choices;149 reaches70/70 attempted
choices but never another complete-model check after its initial point. This
rules out simply extending the20ms preparation allocation as a sufficient fix.
R1041 seals this experiment
(`11ee1bb997c920c0104cfa94464c066fcfa97d28abc78ffbee883282fef09a31`).
See the [combined receipts](CANDIDATE_INITIALIZATION_PILOTS_20261031.json).

The next evidence-backed algorithm target is chronological candidate backtracking
without usable branch explanations. `searchBoundaryCandidates` receives only a
boolean feasibility result; private simplex parameter bounds and substituted
atom bounds currently share one dummy literal. Build a shared explained candidate
search interface, with conservative parameter dependencies for each private
linear premise and conflict, then test backjumping on these public gaps. Account
for candidate-generation dependencies when exhausting a domain: the current
simplex-derived candidate can depend on the entire active prefix. Do not treat
finite sampled-domain exhaustion as an original UNSAT proof. Preserve unwind,
withdrawal and exact original-model validation, and compare against independent
finite-search/reference checks before accepting any improvement. Repeating the
closed seed-only or budget-only probes is not the next step.

Both cores are committed and source-qualified but remain unpromoted; this branch
also retains earlier zero-gain experiments. Do not blindly merge the whole stack
because the constructed initialization benchmark improves. If delivering the
initialization fix alone, assemble a focused final diff on the existing development
branch, retain frozen/history evidence and qualify that actual source before PR
CI/merge. No extra branches/worktrees, no protected-set tuning, and no
`validation/current-main.json` requirement. The last full160 reference remains100
verified Xolver versus118 verified/125 raw Z3; both protected sets and a fresh
multi-program original QCP comparison remain outstanding.


### Explained candidate completion, full-suite regression and cover diversity

Core `d80fb40b` combines immutable candidate-domain passes, explained rational
singleton substitution and canonical residual monomials. The generic finite
search accepts checked partial completions and backjumps using premise and
candidate-generation dependencies. Each arithmetic attempt owns its simplex
facts, domains and explanations; every returned point passes exact original
polynomial validation. Neither failed candidates nor exhausted samples prove
UNSAT. R1064 native qualification passes207 targeted cases/23359 assertions;
all39 R1067 acceptance groups pass,1871 unit cases/986540 assertions. R1068
seals that source and the actual timed149 model, positively replayed by both
Z3 and cvc5 (`a378d6724fe6172ba1d8e633de7aa25a5bfc9865ea97ffe3a30f29556bc50138`).

R1065 plus148 disjoint R1069 inputs form a fresh full160 round with unchanged
60s/one physical CPU/16GiB budgets and initial model capture. Verified counts
are101 main-baseline,100 candidate and118 Z3 (125 raw); PAR-2 is7427.055,
7509.512 and5386.910. Candidate gains149 (baseline timeout, candidate0.165s
SAT), but loses51 and158, so it is not promoted. All actual Xolver SAT models
replay, with no opposite verdict or invalid exported model. Current duplicate
Z3 models on47/108/122 positively replay with both checkers;50/94 retain their
same-hash offline truth evidence and115 has a freshly checked modular
certificate. This affects eligibility only; no old solver timing is substituted.
Seven unconfirmed Z3 UNSATs12/24/27/42/80/114/159 remain excluded. R1070 seals
this negative full-suite result
(`e36bbd0b948b8051ba29d6d83b892d8fc664146e6717e883322d04f093cf41dc`).

158 exposes a general decomposition tradeoff: the baseline samples12 parameters
and retains3 joint equality unknowns, finding a model in about1.1ms. The first
candidate samples only9, but its finite grid misses a needed joint completion.
The repair gives an equality-block cover a short attempt, then tries a smaller
cover using the SAME total time/work allocation and search implementation.
Each cover gets fresh contexts and explanations. Private R1073 passes197
selected cases/22808 assertions. Fresh R1076 restores158 (about0.066s SAT)
and preserves149 (about0.166s SAT); both actual initial models replay with
Z3 and cvc5.51 reverses to a28.125s candidate SAT against a baseline timeout,
despite unchanged LRA critical-path source. Treat51 as timing-sensitive; this
reversal is not a stable cover-search gain or a full-suite conclusion.

A new off-grid unit test initially constructed a fractional polynomial constant
without clearing its denominator. The integer-ring backend returned NullPoly,
then subtraction dereferenced it before model search began. The test now uses
an equivalent integer-coefficient inequality. Core `81291b5d` propagates unsupported
operands through add/subtract/multiply/negate/power in both polynomial backends,
without caching an invalid handle as a valid expression. Private R1083 passes
224 selected cases/22986 assertions, including the corrected off-grid completion
and sentinel/cache-isolation tests. R1079 authenticates both repair prototypes,
actual model replays and the failed diagnostic attempts; these remain distinct
from final-source native qualification. See the
[bounded receipts](EXPLAINED_CANDIDATE_SEARCH_20261031.json).

The immediate next step is to qualify the committed cover-diversity and
unsupported-operand fixes together on Panda1, freeze the actual final binaries,
then repeat full acceptance and a fresh fair160 comparison. Do not promote a
partial-pilot gain or attribute51's timing reversal without further evidence.
The original GCD Xolver/Z3 runs `native_gcd_*_r1071-20261031095116` subsequently
completed all nine original VCs and passed fresh canonical final checks. R1084
authenticates 296 actual native calls per backend (174 SAT/122 UNSAT), 70 unique
independently checked formulas, and one persistent solver process each. This
uses the earlier frozen d80fb40b worker and does not qualify a later kernel.
The proof scripts differ, and no VC is recorded as discharged by the external
SMT post-generation checker; Coq proves the original goals. Native backend
coverage and complete program verification are separately established. Final program-set comparison, both protected sets,
PR CI and postmerge main CI remain outstanding. No extra branch/worktree or
`validation/current-main.json` archive is required.


### Cover diversity accepted; candidate evaluation reuse is the next stage

PR83 merges source65c9cb8c as main `d3b767af`. Exact-head CI41162240789
passes proof-gate and build-test. The main push CI41164344182 is running;
confirm its terminal result before reporting postmerge CI green. R1085 binds
the actual source manifest (`8240f2b4cbaaf1898caa87b8f333bc0d93fdbc67872957099d36ef8c380f72a4`)
to CLI `b9f3e3ff68ba8acf5de5a2b5d050b56de88ed71d9a43304c5cbb066cf2367041`,
SV373a3655 and worker a889508b. All39 R1087 native acceptance groups pass,
including1873 unit cases/986585 assertions and original-model differentials.

The fresh fixed160 round verifies **100 baseline /102 candidate /117 Z3**
(124 raw Z3). Verified PAR-2 is7510.892/7304.941/5485.340. All solves use
60s/one leased physical CPU/16GiB and initial model capture.149 improves from
a baseline timeout to0.166s SAT;158 is restored to about0.067s.51 is also a
candidate-only solve this round (28.293s), but its earlier reversals remain a
timing-sensitivity boundary. There are no lost solves, opposite verdicts or
invalid exported models. Seven unconfirmed Z3 UNSATs12/24/27/42/80/114/159
remain excluded.47 is a Z3 timeout this round: the historical125-raw reference
must not replace the fresh124-raw observation.

Two initial R1086 triads,42/89, suffered later foreign fuzzer occupation of
their leased CPUs. Actual wall-budget violations were617.720s and639.671s;
both original jobs terminate failed and remain preserved. R1094 repeats only
those two COMPLETE triads on newly leased CPUs, with identical frozen binaries
and valid60s budgets. The158 other valid original triads are retained unchanged.
No solver-specific result or fastest timing is selected. R1090 checks the actual
initial Z3 models on108/122 with both Z3 and cvc5;47 has no current SAT model
and is explicitly skipped. Same-input offline truth50/94 and a fresh checked
certificate115 affect eligibility only. R1089 seals all39 groups, the160 valid
triads, excluded infrastructure failures and these truth boundaries:
`b64f30a4e19d6a6211d6242769ea78ffb51fcdce73a37f3b3e97fd47d38abd55`.
The final version remains below Z3. Both protected sets remain unused.

R1091 samples public integer gaps47/108/122.47 spends substantial time in
CandidateModelSearch and repeated NativeTerms materialization;108/122 also
spend time in eager bit-blast and Boolean search. The next small general fix
keeps an evaluation memo for one immutable candidate assignment across all
assertions, invalidates when UF derivation changes assignments, and observes
the deadline during iterative DAG traversal. The candidate remains SAT-only.
Private R1092 passes55 selected cases/230 assertions, including assignment
changes, contradictory shared roots and nested UF derivation. Its identical
4096-depth/512-root constructed DAG improves2.31713s→0.00777564s; the integer
witness positively replays with both independent checkers. R1095's three20s
original-gap profiles ALL still time out. This establishes a local shared-DAG
improvement and a deadline fix, not an original-input solving gain. Qualify the
actual committed implementation, run full acceptance and a fresh full160 round
before considering its merge. Do not repeat the same three profiles as evidence
of a new gain. A final-kernel original multi-program QCP comparison and both
independent protected sets remain required for the full goal.


### Single-model capture and postmerge main CI

PR83's latest main CI41165659029 is fully green on5b8592b0. That commit merges
the retained Draco history without changing the d3b767af source tree; the older
main run was cancelled by the workflow concurrency rule. The frozen baseline
code therefore remains unchanged. No additional current-main archive is needed.

The current candidate has completed all39 native groups and1877 unit cases.
The original R1098 comparison detects six real budget violations, not solver
counterexamples; all excluded reports remain available. The source-only command
inventory R1109 identifies exactly four explicit get-model inputs32/47/108/122.
Native check R1105 and16 tool tests establish one export for the corrected
policy; R1102's earlier isolated import-path failure remains preserved and did
not execute the native CLI probes. Do not overwrite live canonical runners or
mix capture policies without verifying actual recorded commands. The current
correction plan retains150 valid triads, replaces six complete budget-invalid
triads (R1101/R1107) and four complete redundant-export triads (R1108), and keeps
all solver hashes/budgets fixed. R1099's final effective-policy audit and the
updated runner's committed-source qualification are pending. Both protected
sets and the final-kernel original multi-program QCP comparison remain unused
or outstanding; this is not the full goal's completion.


### Candidate evaluation full160 closure (R1099)

All39 R1097 native groups pass,1877 unit cases/986592 assertions. R1099 seals
150 unchanged valid original triads, six complete replacements for actual wall
budget violations, and four complete replacements for redundant Z3 model
exports identified solely from the original input commands. Actual flags are
checked on every selected input before refining capture metadata; original raw
reports, decisions, times and resources are unchanged. All solver versions stay
frozen: delivered b9f3e3ff, candidate aab07fcc, and Z3 44d6ba3c.

Verified counts are101/101/117; Z3 has124 raw decisions and the same seven
unconfirmed UNSATs. There are no gains/losses, opposite verdicts or invalid
exported models. Verified PAR-2 is7398.656/7394.498/5515.109. The small single-round
difference is not an established whole-solver speedup. The shared-DAG/resource
contract fix has a demonstrated local benefit, but the attempt to close original
integer gaps by this change yields no solve gain. R1099 receipt:
`08b4ef8437da387c2df7dcd7201a681110f1f6ee439a41fa4d763b455677673b`.
Do not repeat the closed47/108/122 profiles as a new optimization experiment.
Next work must target a different measured algorithmic failure mechanism.

The final tool change avoids automatically adding -model when the original
script already requests a model and records the new capture policy explicitly.
Its16 tests and native Z3 checks pass. Source32/47/108/122 each has exactly one
explicit request; all other fixed inputs have none. Comments, strings and quoted
symbols cannot masquerade as commands. Mixed capture metadata is rejected by
the summary tests; the R1099 aggregation is permitted only by its independent
per-input command-equivalence check. Final source qualification and PR84 exact
head CI remain required. Both protected sets are untouched, and the final-kernel
original multi-program QCP comparison remains outstanding.

### Shared integer residue components (R1115–R1121)

The measured root cause is starvation of exact modular reasoning behind a
SAT-only portfolio, plus collecting irrelevant quotient and disconnected
variables before the old enumeration cap. Shared coefficient reduction and
component enumeration now run in the Boolean prepass and the NIA algebraic
stage. Every conflict has a complete finite residue justification and original
equality premises. Incomplete search yields no verdict. The existing NIA
controls, LRA/LIA withdrawal policies and public solver API are preserved.

R1115 qualifies committed core 243a267f; R1116 passes all 39 acceptance groups,
1883 cases / 986681 assertions. R1120 seals the full 160 comparison and independent
81-class local regression certificate. Its SHA-256 is
`76dee94deb3cc88f9d4e5d762173aee9a9a6fdc34f01c73dffe292fb56f7c3d2`.
Verified coverage remains 101/101/117; no original gap is closed. The local
19.908s→0.068511s result is retained without claiming whole-suite superiority.

The final source publishes an independent checker and adversarial certificate
tests. Reproduction from the repository root:

```sh
python3 tools/soundness/polynomial_residue_certificate.py check tests/regression/nia/coupled_square_residues_unsat.smt2 docs/audit/COUPLED_SQUARE_RESIDUE_CERTIFICATE.json
```

R1121 must validate that public checker and confirm every native executable,
library and solver source is unchanged before reusing R1120's acceptance and
comparison. Exact final-head PR CI remains a promotion gate. The next capability
work must target original gaps or real QCP validation; the closed early-quadratic
and candidate-cache gap profiles must not be repeated as new experiments.
