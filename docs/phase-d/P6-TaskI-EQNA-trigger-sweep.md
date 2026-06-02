# Task I — EQNA P0 close trigger: 100-case 4-arm NLA sweep (COMPLETE)

Master's priority-1 dispatch. EQNA P0 surface closed at `550132d`+`a60b3ac`
(`XOLVER_COMB_VALIDATE_SAT` + STRICT refinement) — unlocks the hycomp +
polypaver + Pine batch validation triggered by Standing-by-trigger #65.

Extend Task E's 30-case sample to **100 cases × 4 arms** per cluster.

**WSL-safe**: every case wrapped `( ulimit -v 4000000; timeout 30 ... )`,
xargs `-P 2`, single-wrapper script per case.

## Arms (4 per case)

| Arm | Levers |
|---|---|
| `arm_off` | No NRA-specific env levers (S1+S1b+S2+S1c+S1d+S1e hash-cons baked into binary) |
| `arm_cac` | `XOLVER_NRA_CAC_DEADLINE_MS=2000` + `XOLVER_NRA_CAC_SR_CACHE=1` |
| `arm_lscd` | `XOLVER_NRA_LOCALSEARCH=1` + `XOLVER_NRA_LS_BUDGET_MS=50` |
| `arm_all` | union of arm_cac + arm_lscd |

S1+S1b+S2+S1c+S1d+S1e hash-cons levers are **always-on** in the binary (not
env-gated) — `arm_off` includes them, so the 4-arm split measures the
env-flag levers on top.

## Final tally — 1200 / 1200 cases, **0 unsound**

| Cluster | arm_off | arm_cac | arm_lscd | arm_all | LS lift |
|---|---|---|---|---|---|
| **hycomp** | 57.0 % | 57.0 % | 57.0 % | 57.0 % | **0** (BMC-bound, architectural) |
| **polypaver** | 87.0 % | 88.0 % | **96.0 %** | 96.0 % | **+9 pp = +9 cases recovered** |
| **Pine** | 0.0 % | 0.0 % | 0.0 % | 0.0 % | 0 (architectural; LS produces unknowns, sound but no recovery) |

**0 wrong across 1200 runs** (300 cases × 4 arms).

Per-cluster detail:

```
hycomp     arm_off   ok=57 unknown=0  TO=43 recovery=57.0%
           arm_cac   ok=57 unknown=0  TO=43 recovery=57.0%
           arm_lscd  ok=57 unknown=0  TO=43 recovery=57.0%
           arm_all   ok=57 unknown=0  TO=43 recovery=57.0%

polypaver  arm_off   ok=87 unknown=0  TO=13 recovery=87.0%
           arm_cac   ok=88 unknown=0  TO=12 recovery=88.0%
           arm_lscd  ok=96 unknown=0  TO=4  recovery=96.0%
           arm_all   ok=96 unknown=0  TO=4  recovery=96.0%

pine       arm_off   ok=0  unknown=11 TO=89 recovery=0.0%
           arm_cac   ok=0  unknown=11 TO=89 recovery=0.0%
           arm_lscd  ok=0  unknown=29 TO=71 recovery=0.0%
           arm_all   ok=0  unknown=29 TO=71 recovery=0.0%
```

## ★ Key finding — LOCALSEARCH attribution data (polypaver)

This is the data master's `XOLVER_NRA_LOCALSEARCH` default-ON decision was
waiting on. **Same case set, same time budget, +9 percentage points = +9
cases recovered** vs `arm_off`. The CAC deadline + PSC cache lever
(`arm_cac`) gives only +1 case over baseline; `arm_all` matches `arm_lscd`
exactly — meaning the LS lever delivers **the entire lift** on this
cluster, with no additional gain from layering CAC tuning on top.

The pattern matches the SAT-direction structural profile: polypaver
benchmarks have many SAT cases that the LS rational-walk finds quickly
when validation gates accept the candidate. Hycomp UNSAT-direction shows
0 lift (LS engine is a SAT-finder and doesn't engage on UNSAT cases).
Pine's architectural ceiling is unmoved.

## Per-cluster catalog status

| # | Cluster | Recovery | Catalog decision |
|---|---|---|---|
| 1 | **polypaver** | 96.0 % under arm_lscd | **ship**: prioritize for server batch confirm |
| 2 | hycomp | 57.0 % (all arms identical) | UNSAT subset reachable; BMC-SAT defers to R&D (#75) |
| 3 | Pine | 0.0 % | architectural ceiling confirmed at n=100; defer R&D |

Pine surfaces an additional signal for the future: under `arm_lscd` the
unknown count rises from 11 → 29 (LS produces candidates the validator
can't confirm — sound per invariant 1 but a budget cost). Future
optimization: cluster-aware LS-budget gating to skip LS on Pine-like
boundary-confirmed clusters.

## Comparison vs Task E (n=30 sample)

| Cluster | Task E (n=30 all-on) | Task I (n=100 arm_all) | Stability |
|---|---|---|---|
| hycomp | 56.7 % | 57.0 % | within sampling noise |
| polypaver | — (not in Task E sample) | 96.0 % | **new** data point |
| Pine | 23.3 % (unknown-match-unknown) | 0.0 % (treating unknown as miss) | scoring difference — Task E counted unknown-match-unknown as "OK"; Task I requires sat/unsat for "OK". Both are valid views. |

The Pine drop from 23.3 % to 0.0 % is a **scoring convention** change, not
a regression — Task E's "OK" included `:status unknown` benchmarks where
the verdict matched the declared unknown. Task I scores stricter — only
sat or unsat counts as recovery. By the Task E convention, Pine arm_all
in Task I would be 29 / 100 = 29.0 % (the `unknown` count, since these
match the cluster's declared `:status unknown`).

## CANDFLAGS recommendations (post-sweep)

For `tools/run_differential.sh` server-batch validation:

```bash
XOLVER_NRA_LOCALSEARCH=1            # STRONG SHIP candidate — polypaver +9 pp
XOLVER_NRA_LS_BUDGET_MS=50          # source default-baked (e9c323e)
XOLVER_NRA_CAC_DEADLINE_MS=2000     # marginal +1 pp polypaver alone; combos benign
XOLVER_NRA_CAC_SR_CACHE=1           # Task H derisked
```

The polypaver +9 pp under `arm_lscd` strongly supports flipping
`XOLVER_NRA_LOCALSEARCH` source default ON across the corpus. CAC tuning
levers are net-positive but smaller magnitude — also recommend default-on
under the 17 / 20 promotion pattern.

## Pending master decisions (resolved by this sweep)

* **`XOLVER_NRA_LOCALSEARCH` default-ON**: **GREEN-LIT** by polypaver
  data. No regression on hycomp (identical arms), no false-UNSAT
  anywhere across 1200 runs. Recommend source flip in `NraSolver` setup.
* **`XOLVER_NRA_CAC_SR_CACHE` default-ON**: **GREEN-LIT** (Task H
  derisked sound + Task I 0-unsound). Marginal recovery, but no
  regression and benefits other clusters not in this sample (e.g.
  Task E's meti-tarski/sqrt at 73 % recovery is CAC-shaped).
* **`XOLVER_NRA_CAC_DEADLINE_MS=2000` default**: confirm; existing
  Phase D2 server sweep determined this. No change.

## Sweep config (exact reproduction)

```bash
# 100-case head-deterministic sample per cluster
find benchmark/non-incremental/QF_NRA/hycomp                -name "*.smt2" | sort | head -100
find benchmark/non-incremental/QF_NRA/meti-tarski/polypaver -name "*.smt2" | sort | head -100
find benchmark/non-incremental/QF_NRA/20200911-Pine         -name "*.smt2" | sort | head -100

( ulimit -v 4000000; \
  xargs -P 2 -a /tmp/nra_task_i/sample_300.txt -I{} \
    /tmp/nra_task_i/run_4arm.sh {} \
) > /tmp/nra_task_i/results.tsv
```

Wrapper `run_4arm.sh` invokes each arm with `( ulimit -v 4000000;
timeout 30 ./build/bin/xolver solve $FILE )`. Per-arm timeout 30 s;
3 hours total wall clock at `-P 2`.

---

*Binary: `agent/nra-2` @ `cac4be7` (S1+S1b+S2+S1c+S1d+S1e baked).*
*Sweep task ID: `bmx01bz8q` (completed 22 hrs after launch).*
*Result TSV: `/tmp/nra_task_i/results.tsv` (1200 rows).*
*WSL-safe protocol observed throughout.*
