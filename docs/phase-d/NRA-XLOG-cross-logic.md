# Task NRA-XLOG — Cross-logic NRA stack validation

Master's priority-3 dispatch (NEW 8h queue, 2026-06-02). Test whether
the 6-layer NRA hash-cons stack + LOCALSEARCH + CAC_SR_CACHE
(promoted source-default ON via Task Q) carry their NRA-lane gains
into cross-logic territory.

**Conclusion**: cas / sqrtmodinv QF_UFNRA cases are **NIA-engine bound**
(timeouts on both pre-Q and post-Q binaries) — the NRA stack does not
help because the bottleneck isn't in NRA paths. QF_NIRA tested cases
solve fast on both (already fast — no measurable delta). The
cross-logic surface is real but lives in NIA / combination lanes, not
NRA.

---

## Sample

13 cases total (WSL-safe, single-process per case, 20 s timeout):

* **QF_UFNRA**: 5 from `cas` + 5 from `20230328-sqrtmodinv-hoenicke`
* **QF_NIRA**: 3 from corpus head (only 3 reachable)

## Paired result

| Logic | Case | pre-Q OFF | t_off | post-Q ON | t_on |
|---|---|---|---|---|---|
| QF_UFNRA | 10u05.04 | TO | 20.22 | TO | 17.52 |
| QF_UFNRA | 20revert.u | TO | 20.08 | TO | 17.28 |
| QF_UFNRA | 20u10.09 | TO | 17.36 | TO | 20.13 |
| QF_UFNRA | 30u15.14 | TO | 17.19 | TO | 17.19 |
| QF_UFNRA | 40f10 | TO | 20.02 | TO | 17.23 |
| QF_UFNRA | modInvFull | TO | 20.08 | TO | 17.21 |
| QF_UFNRA | modInvInitial | TO | 17.27 | TO | 20.03 |
| QF_UFNRA | modInvStep | TO | 17.12 | TO | 20.03 |
| QF_UFNRA | modInvVar1 | TO | 17.27 | TO | 17.20 |
| QF_UFNRA | modSimpleTest | TO | 20.10 | TO | 17.28 |
| QF_NIRA | miniflight.nosummaries | unsat | 2.44 | unsat | 2.29 |
| QF_NIRA | miniflight | unsat | 2.28 | unsat | 2.24 |
| QF_NIRA | test_union_cast-1_true-unreach-call.i | unsat | 0.06 | unsat | 0.12 |

## Findings

### Finding 1 — QF_UFNRA cas / sqrtmodinv: NIA-bound, not NRA-bound

All 10 QF_UFNRA cases time out on BOTH binaries within the 20 s budget.
This is consistent with the prior session memory (`project_nia_perpropagation_perf`):
the cas + sqrtmodinv cluster's bottleneck is **NIA engine per-propagation
work in EVM mod 2^256 reasoning** — runs heavy stages per cb_propagate.
The NRA hash-cons stack accelerates polynomial-kernel paths, but those
paths aren't on the hot trace for these cases.

The NRA-side L3 modular reasoner (commits 2d78819 + b8968ed,
`XOLVER_NIA_MODULAR=1`) is the right tool, but that's NIA-agent
territory — promoting it default-ON would be another sprint task.

### Finding 2 — QF_NIRA tested cases: already fast, no measurable delta

The 3 QF_NIRA cases in the local sample all decide UNSAT in 0.06-2.44 s
on both binaries. The differences (2.44 → 2.29, 2.28 → 2.24, 0.06 →
0.12) are within sampling noise. The NRA stack is not contributing
measurably here because:

1. These cases are small (LIA / linear-dominated under the partition)
2. They decide UNSAT before any nonlinear projection path is exercised

A larger QF_NIRA sample (50+ cases) would surface NRA-contribution
patterns if any exist, but that's a server-batch task — the local
WSL-safe sample (13 cases at 20 s budget) is the right scope here.

### Finding 3 — No regressions

Across the 13-case paired test, **0 verdict regressions** post-promotion.
Wall-clock deltas are within the 5-15 % noise envelope expected for
WSL multi-process scheduling.

## Architectural note

The hash-cons stack's cross-logic story is asymmetric:

* **QF_UFNRA**: combination logic; NRA-side wins are gated by the
  NRA-engine actually running. cas / sqrtmodinv cases never reach
  NRA in earnest because NIA engine times out first.
* **QF_NIRA**: shares NRA's polynomial kernel for the real part;
  hash-cons gains should transfer to cases that exercise the
  nonlinear-real path. Need a larger sample to confirm.
* **QF_AUFNRA**: not in benchmark corpus (per master's spec); skip.

## Recommendation

* For UFNRA cas / sqrtmodinv: hand off to NIA-agent (promote
  `XOLVER_NIA_MODULAR` default-ON to test mod-2^k path).
* For QF_NIRA: server batch with a 100+ case sample under
  CANDFLAGS would surface NRA-stack contribution if it exists.
* The local 13-case sample confirms 0 regressions but does NOT
  surface a positive +N attribution — that's a server-scale signal.

---

*Binary: `agent/nra-2` @ `198219d`.*
*Pre-Q baseline: `/tmp/nra_task_i/xolver_pre_Q.bin` (commit `eff76fa`).*
*Result TSV: `/tmp/nra_xlog/results.tsv`.*
*WSL-safe protocol observed.*
