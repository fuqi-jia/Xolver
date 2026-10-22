# CI repair after application migration

Status: validation in progress. Do not interpret the historical migration
selection as a passing full suite. Main is updated only after preflight checks.

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
- Preserve arithmetic theory routing when substitution removes the last
  variable but leaves constant relations. `x=1 AND x=0` must still refute `1=0`;
  numeric atoms cannot become freely assignable Boolean literals.
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
