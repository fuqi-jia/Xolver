# CI repair after application migration

Status: full server validation passed. GitHub PR/main checks are tracked in
[PR 28](https://github.com/fuqi-jia/Xolver/pull/28). Main is updated only after
preflight CI succeeds; the user requested pausing after main CI is green.

The failed main run is [39815502975](https://github.com/fuqi-jia/Xolver/actions/runs/39815502975)
for `d173712fd3e0502499729183e50d6136a336d990`:

- `proof-gate` spent its 90-minute job allowance installing system dependencies.
  Ubuntu's Azure mirror stopped making progress. Proof compilation/checking did
  not start. The repaired workflow checks installed packages first and bounds
  access to Ubuntu's signed archive, caches pinned checkers, and builds only the
  solver in the proof lane. Independent DRAT/Alethe checks remain mandatory for
  emitted artifacts; missing certificates remain explicitly reported as before.
- `build-test` compiled successfully, then its runner received a shutdown signal
  during units. The log does not establish why the runner shut down.

Server diagnosis of all 1505 registered unit cases (individually, 30-second and
3-GiB limits) found two deep-term failures, two incorrect SAT results, two SL
budget failures and two timeouts. The timeouts are diagnostic observations,
not proof that those tests fail under the normal CI allowance.

Implemented repairs:

- Rewrite maximal singly used associative chains before postorder processing,
  avoiding quadratic storage for all prefixes of a deep sum. Preserve shared
  arithmetic nodes instead of expanding a compact DAG exponentially.
- Select arithmetic domains once for both solver construction and atom registration.
  Preserve arithmetic theory routing when substitution removes the last
  variable but leaves constant relations. `x=1 AND x=0` must still refute `1=0`;
  numeric atoms cannot become freely assignable Boolean literals.
- Grow polynomial accumulation storage geometrically instead of reserving the
  exact next size on every append; handle self-aliases before changing storage.
- Export separate proof artifacts and replay inputs for every incremental query.
  Validate every query, including earlier UNSATs, and reject missing responses.
  Keep proof artifact directories in GitHub uploads (including hidden paths).
- Open positive existential SL witnesses only through conjunction, disjunction
  and separating conjunction. Retain binder scope across negation, universals,
  wand and data positions. Hide fresh witnesses from public model assignments.
- Split heap-dependent conditional predicate arguments at the calling heap,
  before predicate bodies change heaps through star/wand.
- Update SOMTParser through `git submodule update --remote --no-fetch` to upstream
  main `7e53cb1056843d4fa4e6a8d80f9724e880753a34`, which merged
  [SOMTParser PR 63](https://github.com/fuqi-jia/SOMTParser/pull/63). No dependency
  source is patched locally. The existing upstream change implements integer
  division's [SMT-LIB left-associative semantics](https://smt-lib.org/theories-Ints.shtml).

Heavy validation uses Panda1/ExperimentOS and the existing
`/pub/data/jiafq/xolver/build` with its writer lock. No per-run build tree is
created. GitHub validates both the default build and proof-enabled build.

## Final server validation

ExperimentOS `xolver-ci-repair-r8` (`762bc2d4bbf4`) built the final production
sources and passed 116 focused units, architecture, standalone evidence and the
Python/CLI harness tests. `xolver-ci-complete-r2` (`c02beb0108bb`) then used those
frozen binaries and frozen test inputs with no unit filters:

| Check | Result |
| --- | --- |
| Full unit suite | 1507/1507; 575758 assertions; no skipped tests |
| Regression suite | 850/850, 240-second per-case deadline |
| PA differential suite | 115/115; 0 wrong/error/unknown/timeout |
| Independent PA oracle calls | 230 Z3/cvc5 checks; 15 model pins |
| PA certificate output | 115 generated schemas; not a formal end-to-end proof |
| Server proof corpus (DRAT) | 104 files, including both queries of the incremental input; 0 rejected/errors |
| Source architecture | 545 files, 11 layers, 0 violations |
| Control contract | 161 typed controls / 237 sites, unchanged by this repair |

The server has DRAT but no Carcara: 22 files have complete propositional proofs,
72 have checked Boolean skeletons with assumed theory lemmas, and 10 have no
proof. GitHub separately installs Carcara and checks the emitted Alethe theory
certificates. Missing proof coverage remains explicit; no checker rejection is
waived. The server's previous full run failed two units and one proof export;
those failed results are retained alongside the passing final run.

The 30,000-level nonlinear term unit took 49.80 seconds in `ci-repair-r6` and
0.21 seconds in `ci-repair-r8` on Panda1 after fixing repeated exact allocation.
This is a focused workload observation, not a general solver speedup claim.
The separately documented intermittent NRA search performance has no claimed
root-cause fix; the final full regression did pass its normal deadline.

Source, binary and input hashes, logs, ExperimentOS identities and proof artifacts
are retained in the CI repair evidence archive described in
[CI-REPAIR-VALIDATION.json](CI-REPAIR-VALIDATION.json). Historical migration failures
in `APPLICATION-VALIDATION.json` remain unchanged.
