# SOMTParser native-DAG migration: server evidence

All compilation and solver execution described here run on Panda1 through
ExperimentOS. Writers reuse `/pub/data/jiafq/xolver/build` under its writer
lock. Validation retains frozen binaries and logs, not extra build trees.
`native-terms-rN` labels are distinct from the earlier `architecture-rN` labels.

## Completed checks

| Version | Unit tests | File regressions | Status |
|---|---|---|---|
| Native R4 | 1542/1543 | 818/820 | One fixture expected noncanonical `Geq`; NRA 155 and 200 timed out |
| Native R5 | 1546/1546, 513175 assertions | 819/820 | NRA 200 recovered; NRA 155 still timed out at 240 seconds |
| Native R6 | 1547/1547, 513181 assertions | 819/820 | Native operator reconstruction deduplicates; NRA 155 still times out |
| Native R7 | Build failed | Not run | New test used unsupported multiargument doctest `CAPTURE`; corrected in R8 |
| Native R8 | Preflight 30/31; 2198 assertions passed | Not run | SAT-only test harness lacked the observer required by the production backend; corrected in R9 |
| Native R9 | 1553/1553, 515181 assertions | 819/820 | NRA 155 still timed out at 240 seconds |
| Native R10 | 1553/1553, 515181 assertions | 819/820 | NRA 155 aborted allocating memory under the 16 GB experiment limit |
| Native R11 | 1557/1557, 515429 assertions | 819/820 | NRA 155 still failed allocating memory; verbose replay identified presolve expansion |
| Native R12 | 1562/1562, 515473 assertions | 820/820 | Transactional, bounded presolve substitution recovered NRA 155 |
| Native R13 | Preflight 41/42; eight assertions failed | Not run | New chain-comparison tests exposed a duplicate parser dispatcher |
| Native R14 | 1564/1564, 515535 assertions | 823/823 | Single operator dispatcher; 200 syntax/expansion pairs agree with both oracles |
| Native R15 | 1566/1566, 515691 assertions | 825/825 | New 180-pair differential finds one wrong SAT from Boolean `distinct` constant removal |
| Native R16 | 1567/1567, 515859 assertions | 827/827 | All 180 repeated expansion pairs agree; 120 model cases agree and 82 SAT assignments validate |
| Native R17 | Build failed | Not run | SL enumeration helper collided with `std::advance`; corrected before R18 |
| Native R18 | 1576/1576, 528788 assertions | 827/827 | Boolean SL core; all 52 tool tests and all seven suite return codes pass |
| Native R20 | 1577/1577, 528793 assertions | 827/827 | SL reachability and state-size accounting; 52 tool tests and 907 frozen inputs verified |
| Native R21 | Preflight 57/59 | Not run | Build succeeded; two native SL fixtures failed because `QF_ALL` was not recognized |
| Native R22 | 1583/1583, 528923 assertions | 833/833 | Direct native SL entry, exact integer heap models, reset/scope fixes; 58 tool tests and 915 frozen inputs verified |
| Native R23 | Test compilation failed | Not run | Solver/CLI compiled; new Result comparisons needed doctest parenthesization, corrected in R25 |
| Native R25 | 1585/1585, 529034 assertions | 833/833 | Direct native PA, optional QE obligations, assumption-aware dispatch and automatic CTest registration; all seven suite return codes pass |
| Native R27 | 1588/1588, 539335 assertions | 833/833 | Fixed-stack SL heap search, shared search/checking budget and per-stack concrete enumeration; 66 tool tests and all seven suite return codes pass |

The R10 focused experiment also reproduced the allocation failure under its
8 GB limit. Moving projection to candidate-model checks did not by itself
resolve the regression. R11 added an exact monomial affine relaxation before
projection, but its presolve expansion could still exhaust memory first.
R12 runs the relaxation before presolve and bounds substitution expansion before
committing it. The focused NRA 155 case now returns UNSAT in 1.795 seconds.

The R8 harness failure threw before its SAT checks. R9 forwards its clauses to
the real SAT backend without registering theory observers, deliberately leaving
the nonlinear decision procedure absent. This isolates whether the new
polynomial-literal clauses preserve both consistent assignments and reject
both contradictory assignments.

Native R5 also completed:

- 600 combination cases: 582 definite results matched both oracles, 18 unknown,
  zero wrong results, crashes, timeouts or oracle skips.
- 300 PA cases: 290 cases with definite answers from both oracles; 22 candidate
  unknowns overall, including two in the 10 oracle-skip cases. No wrong verdicts.
- 120 PA model cases: all verdicts matched; all 73 SAT models validated by
  adding their assignments to the original quantified queries and running both
  Z3 and cvc5.
- 30 Python tests; the standalone evidence checker; 40 CLI/tool tests.
- Proof corpus: 5 complete CNF refutations, 32 skeletons, 9 without proof,
  zero rejected artifacts or execution errors. Skeletons are not SMT proofs.

The 600-case result has **18**, not 19, unknowns. The earlier architecture
baseline had 19; the runs must not be conflated.

Native R9's separate 600-case combination run obtained 583 definite results and
17 unknowns, with zero wrong results, crashes, timeouts or oracle skips. Its
120-case PA model run again checked all 73 SAT models with both oracles.

Native R12 additionally completed:

- 600 combination cases: 583 definite results, 17 unknowns; no wrong results,
  crashes, timeouts or oracle skips.
- 300 PA cases: 290 agreed oracle answers, 22 candidate unknowns; no wrong
  results, crashes or timeouts. The ten oracle-skip cases remain explicit.
- 120 PA model cases: all verdicts matched, all 73 SAT models checked with both
  oracles, no unavailable or rejected models.
- 320 new NRA cases: 286 agreed oracle answers, 34 oracle skips, nine candidate
  timeouts; no observed wrong answers, crashes or unknown returns. Of these,
  240 have constructed witnesses or affine contradictions. The timeout count
  prevents claiming complete success from the experiment's terminal status.
- Python tests (30), CLI/tool tests (40), standalone checker and architecture
  checks passed. The proof corpus remains 5 complete CNF refutations, 32
  skeletons and 9 missing proofs; this is not complete SMT proof coverage.

**New counterexamples supersede any broader interpretation of R12's passing
regression suite.** The PA proof-replay fixtures found three wrong SAT answers:
simultaneous let bindings, Boolean equality with three operands, and
`exists x:Int. 0 < x < 1`. These inputs were absent from the original 820 cases.
R13 fixed let/equality but missed the separate ordinary-expression dispatcher.
R14 removes that duplicate code. Its new targeted tests pass, and 200 pairs
(400 inputs) match between original syntax, explicit expansion, Xolver, Z3 and
cvc5 with no inconclusive cases. Its complete unit and file-regression suites
also pass. This establishes the stated test coverage, not a general correctness
theorem.

R14 also passes all 30 Python tests. Its fixed 48-case, three-repetition
paired performance sample has no disagreements, errors, unknowns or timeouts.
The geometric-mean speedup is 0.97516 with case-bootstrap 95% interval
[0.84658, 1.09256]; it does not establish a performance improvement.
These results are in the verified
[terminal R6/R14 manifest](evidence/pa-isabelle-r6-final-evidence.tar.manifest.json).

R15 adds 25 quantified semantic fixtures, each through the native and rewritten
paths with let preservation enabled and disabled. They exercise Boolean
quantifier alternation, Boolean/integer scope order, n-ary Boolean connectives,
integer `ite/abs`, quantified conditions and signed division of piecewise
terms. A separate test reconstructs both a negative free integer and a free
Boolean while excluding bound variables and local witnesses from the model.
The server preflight passes. The 180 independent expansion pairs finish with
180 definite comparisons and one mismatch: `(distinct true false false false)`
incorrectly becomes true, also under unused Boolean quantifiers.
The expanded source and both oracles say UNSAT; R15 says SAT on the original.
R16 removes that constant-dropping transformation and fixes a second bug in
the binary construction API: `distinct (not p) q` must simplify to `p = q`,
not `p != q`. Exhaustive small Boolean constant tuples and all assignments/
negation combinations cover both parser and binary construction paths.
R15 does not export native QE certificates.

R16 also freezes the Python drivers, tool tests, regression files and known-gap
inputs while holding the source/build writer lock, and checks their hashes and
permissions after testing. Architecture inspection runs before unlocking.
Only binaries and small input/source artifacts are frozen; all compilation
continues in the single shared build directory. This removes the race in which
a later overlay could change the inputs of an already-running regression.

R16's repeated differential uses exactly the same 360 input hashes as R15;
all 180 pairs now agree across syntax, expansion and both oracles.
The additional 120 mixed-quantifier model queries all match both oracles.
All 82 SAT assignments validate when pinned into the original formulas;
there are no unavailable/rejected models, unknowns, timeouts or oracle skips.
The model harness reuses the common invocation/numeral helpers instead of
maintaining duplicate implementations, and archives its exact source files.
Both runs use the frozen CLI hash recorded below.
All seven full-suite return codes are zero, including the standalone checker,
architecture checks and integrity verification of all 906 frozen input/driver
files. All 51 CLI/tool tests and the separately rebuilt Python bindings' 30
tests pass. Independent replay accepts 45 PA claims and rejects all four deliberate
false-claim/helper controls; its scope is recorded in [PA-ISABELLE.md](PA-ISABELLE.md).

The later validation entry accepts an overlay as its second argument, applying
it under the same writer lock as configuration, compilation and input freezing.
It also rejects an existing output label, preserving earlier failure evidence.
Two local scheduling tests cover writer exclusion, applying the overlay before
configuration, rejecting label reuse and retaining frozen inputs after source
changes. This entry extension postdates the R16 server source snapshot; R16
itself exercises the frozen-input path.

## Native SL entry and model evidence (R22)

The new path consumes SOMTParser nodes directly, without `Kind`/`TermExpr`
conversion. It supports the quantifier-free equality fragment over `(Int Int)`
heaps, free Booleans and arbitrarily nested Boolean/spatial connectives.
The model contains exact integer addresses/data and a separately interpreted
nil. Model export and spatial get-value are covered, as are API assumptions,
push/pop, script reset, reset-assertions, global declarations and pop underflow.
All seven full-suite return codes are zero. Other legacy theory consumers still
use the temporary `Kind`/`TermExpr` interface; this is not its complete removal.

The 240 frozen R20 inputs now run through the actual CLI:

- All 240 agree with the separately frozen R20 SL library results.
- 233 agree with definite cvc5 results; cvc5 returns Unknown for the same seven
  original cases (28, 78, 96, 104, 147, 185, 236).
- Xolver has zero unknowns, errors, timeouts or disagreements.
- All 164 SAT models are exported. Pinning every scalar, nil and exact heap into
  the original input gives 163 cvc5 SAT results, one Unknown (236), no rejected
  or malformed models.

The strict differential experiment remains **failed**, because oracle skips
are not silently converted to success. The independent Coq run separately
checks the exact case-236 model (`x=1`, `y=0`, `nil=0`, empty heap) over integer
locations and integer data. `case236_iff_non_nil` proves its stronger semantic
characterization for all valid heaps; `native_case236_empty_model` specializes
it to the exported model. This is a manual translation of that SMT input,
not a verified SMT translator, a general SL certificate pipeline, or a C++
refinement theorem. The first Coq R5 attempt failed at a tactic; R6 corrects it.
R6 passes both coqc and coqchk, with 13 closed theorem reports: seven SL and six
previous arithmetic/equality rules. Both failures (native R21 and Coq R5) are
preserved alongside the passing runs.

CLI SHA256: `e6fe93adff51b3a40b319ba64d12dee3802dbe7079f3ab5f306f93afee7d73f5`.
R22 source overlay SHA256:
`d351a35ff9594ef6bddfb458e11c560764f56fadddac0fe510376a1ce3a5cce9`.
The [native SL evidence manifest](evidence/sl-native-r22-evidence.tar.manifest.json)
binds the frozen inputs, observations, model pins, Coq sources/logs, job records
and source/binary hashes. All 2302 members were verified after download; archive
SHA256 is `66728bd87ae0fda1da6b3b7e150b51d66373a85ab8041b77ff708da429f491ab`.
At collection, verification also matched all 743 recorded C/C++ source/header
files to the worktree, all 240 original inputs to R20, and the Coq source
to the R6 proof record. See the
[verification record](evidence/sl-native-r22-verification.json).
Exact source overlays and all delta ancestors are
retained in [the source index](evidence/native-source-overlays/index.json).
The [SL report](SEPARATION-BOOLEAN.md) states the domain and proof boundaries.

## Memory safety

A focused ASan/UBSan experiment compiled the archived Boolean purifier and the
fixed purifier against the same dependencies. The old code reproduced a
heap-use-after-free: `vector::push_back` invalidated the parent frame before its
context field was read. The fixed version passed. This is focused sanitizer
coverage, not an ASan run of the whole solver.

Native ownership also has explicit regressions for external handles surviving
manager release, 50000-deep DAG destruction, iterative structural equality,
bound-variable identity, shared operator reconstruction and numeric sorts.

## Performance boundary

Native R5 versus frozen `architecture-r9`, 48 existing cases and three
alternating repetitions per case:

- 48 comparable cases, no verdict differences or timeouts.
- Baseline/candidate geometric mean: **1.017267732**.
- Case-bootstrap 95% interval: **[0.970798767, 1.074862702]**.

This does not demonstrate a significant speedup. The three-case focused suite
separately retains the NRA regression that the 48-case sample misses:
NRA 155 takes about 0.43 seconds in the old baseline and exceeds 120 seconds in
all three R5 repetitions. R6 and R8 also time out at 60 seconds in their focused
checks. NRA 200 returns SAT in about 34–37 seconds after the purifier repair.
An aggregate over only comparable cases must not conceal the omitted timeout.

Native R9's 48-case paired run had geometric mean 0.96020890827079 and a
case-bootstrap 95% interval of [0.8404118575180896, 1.0566349229583754],
with 48 comparable cases and no errors, timeouts or disagreements. This also
does not demonstrate a significant speedup.

Sampling the slow NRA case found most recorded stacks in nonlinear projection
and resultant construction during partial-assignment propagation. Work is
continuing on scheduling as well as mathematical atom identity. Sampling runs
are diagnostic; their timings are not the paired performance measurement.

R12's original 48-case task failed before measurement because its configuration
referenced nonexistent `architecture-r12/xolver`. The failed EOS run is retained.
The corrected task uses the original frozen `architecture-r9` baseline and a
separate evidence directory. All 48 cases, three repetitions each, completed
without verdict differences, errors, timeouts or unknowns. Baseline/candidate
geometric mean is **0.983994821**, 95% case-bootstrap interval
**[0.851933338, 1.104999370]**: no significant speedup has been demonstrated.
The separate focused NRA 155 case recovered from timeout/allocation failure,
but at 1.795 seconds still trails the roughly 0.42-second old baseline.

## Provenance

The [SL R17–R20 evidence manifest](evidence/sl-core-r20-evidence.tar.manifest.json)
binds 2715 records, all individually SHA256-verified after download. The archive
SHA256 is `d973b8338a8905a0625f9c58c43c3ed5bb856468ed70890947c25b58d337f315`.
It preserves the R17 compile failure, successful R18/R20 native suites,
the two incomplete external SL comparisons, and the successful Coq replay.
Details and the location-domain correction are in
[SEPARATION-BOOLEAN.md](SEPARATION-BOOLEAN.md). These SL tests exercise the
library API; the CLI is unchanged because SL parsing/dispatch is not wired yet.

The [source-overlay index](evidence/native-source-overlays/index.json) preserves
20 exact source archives with their full delta ancestry back to the complete
`architecture-final` overlay. Their hashes are verified; manifests retain the
original base revision and parent paths. They total about 4.5 MB and contain
source snapshots, not build trees. Unsubmitted R19 is not presented as a
validated experiment.

| Version | CLI SHA256 |
|---|---|
| Native R4 | `aba961a055e625e31776279d97769c1728d8dd312f0f5853fcdb62c8870082c2` |
| Native R5 | `a8590ee2eef7dd14ce6ec88dc2ff709d5e06cb4e17e42be7740d9027e43931fa` |
| Native R6 | `f98fd1bca76c2bade4f17df6be65642164c7966ade9a2e3095e29f2a7cbcbf28` |
| Native R10 | `a55eace310f3915cac569026c9f07635ed41f45bfcbe4a4a872a6fecadebe4a2` |
| Native R12 | `936df65d7681e9ea1b1817f948759d1b5d38cf1bd33bdf5b44c8f4bf007e5fc6` |
| Native R14 | `14bab30f9c6c6235183753ff85a4693d754897ff546f62e61322cfbee9bad69f` |
| Native R16 | `67385c69068762d44b8c746323e9c63d0f8f71d478c4c0de2a4d87c3c64e2193` |

The [R4–R7 manifest](evidence/native-r4-r7-evidence.tar.manifest.json) binds
992 records by SHA256. The archive SHA256 is
`b790cfa684bea400189f9b2133ef62f9c6884229d21d54f534d76301c8372c7e`.
Its extracted [EOS index](evidence/native-r4-r7/native-r4-r7-evidence.tar-eos-runs.json)
contains run identifiers, commands and statuses. Earlier failed migrations are
retained separately in `evidence/native-failures-r1-r3/`.
Each native source overlay has a `native-terms-rN-source.json` manifest; submodule
edits are included explicitly and are not represented by a gitlink alone.

The [R15 full-suite manifest](evidence/native-r15-evidence.tar.manifest.json)
binds 21 verified records, archive SHA256
`51b6bf3788e70f71bddaa5f5d26e0fa986ab99bd5835d090110893428e9d7264`.
The [R16 semantics/model manifest](evidence/pa-r16-semantic-evidence.tar.manifest.json)
binds 810 verified records, including all differential/model inputs and the
Isabelle R8 failure. Archive SHA256:
`69b881b23ae491716b296f031407881d692fd94492360aa8eb749546133feb92`.
The [R16/R9 final manifest](evidence/native-r16-final-evidence.tar.manifest.json)
binds 1200 verified records, including the frozen validation inputs/drivers,
full native and Python suites, all 45 kernel-checked claims and all four
negative controls. All three EOS records are terminal successes.
Archive SHA256:
`5f3658adefc7ba4ddd3408f60c4127568e2154cb98b5b54fa9bd408b8953f712`.

The [R8–R10 manifest](evidence/native-r8-r10-evidence.tar.manifest.json) binds
413 records, all verified after download. Archive SHA256:
`e8b8906f6d4852ef449a406cbfb80eb881a108f71eae241710c63c5a9fe1a503`.
The archive includes the R9 combination and PA-model runs and preserves the
R10 allocation failures alongside passing unit results.

The [R11–R12 manifest](evidence/native-r11-r12-evidence.tar.manifest.json) binds
1259 records, all verified after download. Archive SHA256:
`3fca6778139293b1046d9551f0c7f8906761121d7707202a513ae86a3b9a4435`.
It includes the R12 full regression, differential/model evidence, and the
original performance configuration failure. The corrected performance run
was collected separately.

The [corrected R12 performance manifest](evidence/native-r12-performance-retry-evidence.tar.manifest.json)
binds five verified records, archive SHA256
`d6886d258611ad6a0cbbb2c43a194c9213c7ffed1999e601dd767e72619c6586`.
The [R14 syntax manifest](evidence/pa-syntax-r14-evidence.tar.manifest.json)
binds 405 verified records, including all 400 original/expanded inputs, archive
SHA256 `8f496d9128d426cdef5f242dc7abc07c3ef18bea8b2eb57880f6364f01f56b33`.
The [PA startup/R13 failure manifest](evidence/pa-native-failures-evidence.tar.manifest.json)
retains 358 verified records, archive SHA256
`5aa266d4b9d6f0d261c1945d3e932d93536571c0383c0ccc8ee1a15ffff5f46a`.

The [R14 full-suite manifest](evidence/native-r14-evidence.tar.manifest.json)
binds 21 verified records, archive SHA256
`98e20dfacaa8fbfca68fe076eceacfdd9a6b0dd947fc25935dd36cb83b7292ee`.
All six suite return codes are zero, including the 47 CLI/tool tests and the
standalone checker. Independent PA kernel-replay evidence has its own
[scope and validation report](PA-ISABELLE.md).

## Still open

Passing suites and independently checked claims have the versioned coverage
reported above; later counterexamples supersede broader claims about older
versions. Subsequent source and proof-tool changes require their own validation.
Typed configuration
does not mean every legacy experimental policy has been removed. Complete PA
elimination certificates, general separation logic and end-to-end verification
of the C++ implementation remain outstanding; these tests and the existing
small Coq kernels do not establish those claims.

## Native PA migration and regression registration (R25/R26)

Native PA reads SOMTParser nodes directly, without the general Kind/TermExpr
compatibility layer. Its affine/divisibility formula belongs to contracts;
serialization of optional QE obligations belongs to evidence. Architecture
checks reject the old compatibility vocabulary in the PA implementation.
The runtime now considers quantified assumptions when selecting PA dispatch.

The frozen Native R25 CLI hash is
`f3faf2a04dcb69b67dc94d85d27e9844b03c942e885ddd804efc90627f25e972`.
PA-native R25 passes all 200 syntax and 180 piecewise original/expanded pairs
against Z3 and cvc5, with no inconclusive pairs. The separate 120-case piecewise
model suite checks all verdicts and all 82 SAT assignments with both oracles: no
unknowns, timeouts, disagreements, rejected models or skipped models. These are
new migration checks, not evidence that all historical PA unknowns are solved.
Native-certificate R1 separately checks 23 original queries, 46 emitted QE steps
and three returned models; both false-step and false-model controls are rejected.

CTest previously omitted the SL and UFDTLIA directories from its manual logic
list. Registration now follows the regression directories automatically. R26
confirms all 25 directories are registered and both previously omitted groups
pass using the frozen R25 binary. The preceding R24 registration attempt stopped
before applying its overlay because the R23 unit build had failed and no frozen
R23 binary existed. Its failed scheduler record is preserved; it is not counted
as test coverage.

Per the user's 2026-10-21 clarification, the task is SMT solver implementation
and validation. Formally proving the input translator, transformation composition
or C++ implementation is outside the delivery requirements. PA/SL solving,
models, optional certificates, reliability, efficiency and regression/scheduling
work remain in scope.

R25's full validation completes with all seven return codes zero: unit tests,
file regressions, Python tool tests, known-gap handling, the standalone checker,
architecture boundaries and frozen-input integrity. The source overlay SHA256 is
`4e9c0e8891a835693271b9aab2547f80ea8ccec22877a437ada0a9fe96b7db50`;
its delta parent is R23 (the R24 overlay was never applied). Logs, source and
certificate inputs, rejected-control evidence and scheduler records are archived
in [pa-native-r25 evidence](evidence/pa-native-r25/); the hash verification summary
is [pa-native-r25-verification.json](evidence/pa-native-r25-verification.json).
The complete source overlay ancestry remains in `evidence/native-source-overlays/`.
No extra C++ build tree or Isabelle heap tree is archived.

Collection verifies all 2257 archive members, all 918 frozen test/driver inputs,
880 generated differential input hashes and all 747 C/C++ files recorded in the
R25 source manifest against the current worktree. The evidence archive SHA256 is
`af52756551b6ba2dd45681d219120e2bbf4e4669ce291d556af6ad4e4636fe9e`.
All 66 Python tool tests run on the server without skips.

## R27: reusable heap search for theory combination

R27 separates stack-arrangement selection from the Boolean SL heap search.
The existing equality-only solver calls `detail::solveHeap`, which can also be
called by a future arithmetic combination layer. The prepared formula and work
budget are shared across candidates; independent witness checking is charged to
that budget. A fixed-stack UNSAT only excludes that stack. Invalid stacks and
resource exhaustion cannot produce UNSAT.

Three new unit cases cover nonconsecutive address values, nil, aliasing under
magic wand, budget reuse and insufficient witness-checking budget. The randomized
concrete-heap test now checks every one of 80 formulas under all nine generated
stacks, rather than stopping after its first satisfiable stack. All 720 fixed-stack
answers agree with concrete enumeration. Preflight passes 66 tests and 26364
assertions; the complete unit suite passes 1588 tests and 539335 assertions with
zero failures or skips. All 833 file regressions and all 66 Python tool tests pass.
The standalone checker, known-gap handling, architecture boundaries and frozen
input integrity also return zero. This run neither implements the PA/SL arithmetic
connection nor establishes a solver-wide speedup.

ExperimentOS experiment `5aca0db29f56` (`xolver-native-terms-r27`) completed
successfully on Panda1, using the shared incremental build. Its source overlay
SHA256 is `2e8e50ab2328d1236accf153c7a8bbf3c4e5e3597a38f4436f7f28dab6671839`,
with R25 as its delta parent. Evidence is stored in
[sl-heap-r27](evidence/sl-heap-r27/), with the reproducible verification script and
experiment specification in [sl-heap-r27-provenance](evidence/sl-heap-r27-provenance/).
Collection verifies all 944 archive members, 918 frozen inputs and 748 recorded
C/C++ source/header files against the current worktree. The archive SHA256 is
`a7fc9bebbc90c192ffd211606528daf05588480bf19c2986995d508cfad57a1b`.
The [verification summary](evidence/sl-heap-r27-verification.json) also confirms
the successful terminal state and all seven metrics for run `d028150b346d`.

## R33: native arithmetic and separation logic combination

The PA/SL path now combines affine integer terms, constant nonzero div/mod,
ite/abs, Boolean predicates, star and wand over an Int-to-Int heap. It consumes
SOMTParser nodes directly, uses the existing theory-specific PA/SL representations,
and shares one budget across import, arithmetic decisions, heap search and
independent model checks. Arithmetic `get-value` preserves the exported stack,
nil and heap interpretation.

Three changes address the intermediate explosion found by server testing:

- PA substitutes exact affine witnesses while retaining the divisibility
  condition introduced by non-unit coefficients. A singleton reconstruction
  interval is checked directly instead of enumerating its entire period.
- Necessary stack conditions account for disjoint mandatory allocations,
  agreeing singleton heaps and heap-independent wand antecedents. Boolean
  polarity and spatial antecedents are preserved.
- Rejected heap candidates produce a direct disjunction over the observations
  that determine heap truth: explicit pure relations, address/nil aliasing and
  equality between mentioned records. Unobserved data/address cross-equalities
  no longer generate separate candidates. Explicit cross-relations remain part
  of the blocking clause.

The final source overlay SHA256 is
`6a21ac4a2067528cbb2a96af418fdd64ebf5bdb72200fb3e885eee531f0f0525`.
R33's ExperimentOS experiment is `4f52a5a2e4ae`, run `3ec9e29b9f87`.
Compilation and solver tests ran on Panda1 using the existing incremental build
and its writer lock. No local C++ compilation or solver benchmark was used.

| Validation | Result |
| --- | --- |
| R33 focused preflight | 74 tests, 27075 assertions, all pass |
| R33 complete unit suite | 1596 tests, 540046 assertions, zero failures or skips |
| R33 file regressions | 841 pass |
| R33 Python tool tests | 67 pass, zero skips |
| Checker, architecture, known-gap handling, frozen-input integrity | All return zero |
| PA syntax and piecewise equivalence | 200 + 180 input pairs agree with Z3 and cvc5; zero inconclusive pairs |
| PA free-variable model corpus | 120 cases; all 82 SAT models accepted with assignments pinned in both oracles |
| SL arithmetic with nil explicitly fixed | 160 determinate cases agree with cvc5; all 116 SAT models accepted |
| Historical SL formulas shifted into arithmetic | 240 agree with their original CLI and library verdicts; zero unknown, error or timeout; 164 checked SAT models |
| Original arithmetic corpus with mixed nil constraints | 160 determinate results; 159 agree, one oracle inconsistency described below; all 118 SAT models accepted |

The PA differential uses R31, whose six recorded PA implementation/contract/model
checker files are byte-identical to R33. The final SL differential and equivalent
formula replay use R33's frozen binary. The arithmetic input hashes are identical
between the original R31 run and the R33 replay: its eight budget-exhausted cases
are resolved. The 240 transformed input hashes are likewise identical between
R32 and R33: its three budget-exhausted cases are resolved. None of these results
claims to close the separate historical PA hard-case corpus.

### Preserved oracle inconsistency

The installed cvc5 is `1.3.4 [git f3b21c4 on branch HEAD]`. On arithmetic case 66,
it reports UNSAT for the original query but SAT after adding Xolver's concrete
stack/heap/nil assignments. This also reproduces on:

```smt2
(set-logic ALL)
(declare-heap (Int Int))
(assert (and sep.emp (wand (pto (- 5) 1) (pto 2 1))))
(check-sat)
```

The empty heap with nil = -5 satisfies the formula: its wand antecedent cannot
allocate nil. Adding `(assert (= (as sep.nil Int) (- 5)))` makes both solvers
return SAT; fixing nil to zero makes both return UNSAT. The diagnostic records
eight original/minimal variants, exact solver versions and binary hashes.
The raw mixed-nil differential remains **failed** under its strict zero-disagreement
criterion. The separate fixed-nil corpus does not replace or rewrite that record.

### Evidence and remaining scope

The [verification summary](evidence/sl-arithmetic-r33-verification.json) records
all twelve terminal runs, including failed intermediate differentials. The
[reproducible verifier and experiment specifications](evidence/sl-arithmetic-r33-provenance/)
check 7184 archived members, frozen test inputs, generated input hashes, binary
hash references and source provenance. All 752 recorded C/C++ files match the
source manifest on both the server and the current local worktree. Reviewer-facing
logs, reports and the minimal oracle reproductions are in
[sl-arithmetic-r33](evidence/sl-arithmetic-r33/). Full frozen inputs remain in the
archive without copying another build tree.

The evidence archive SHA256 is
`86fd10117994b8100cb9340e1c8f943fbcd952fc3aa71463dc8aa57b50e8af3b`.
R28, R29 and R30 preflight failures remain in their separately verified
`sl-arithmetic-r28-failed`, `sl-arithmetic-r29-failed` and
`sl-arithmetic-r30-failed` evidence archives. Their source overlays and the full
delta chain through R33 remain in `evidence/native-source-overlays/`.

This establishes the tested quantifier-free arithmetic/SL combination, not full
quantified or inductive SL, complete solver certificate coverage, resolution of
every historical unknown, or a measured solver-wide speedup. Whole-C++ formal
refinement is outside the user-requested scope; sound SMT verdicts, models and
reproducible validation remain the requirements.
