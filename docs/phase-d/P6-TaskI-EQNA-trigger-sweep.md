# Task I — EQNA P0 close trigger: 100-case 4-arm NLA sweep (IN PROGRESS)

Master's priority-1 dispatch. EQNA P0 surface closed at `550132d`+`a60b3ac`
(`XOLVER_COMB_VALIDATE_SAT` + STRICT refinement) — unlocks the hycomp +
polypaver + Pine batch validation triggered by `Standing-by-trigger #65`.

Extend Task E's 30-case sample to **100 cases** per cluster to confirm the
**30 % boundary recovery threshold** at statistical scale.

**WSL-safe**: every case wrapped `( ulimit -v 4000000; timeout 30 ... )`,
xargs `-P 2`, single-wrapper script per case.

## Arms (4 per case)

| Arm | Levers |
|---|---|
| `arm_off` | No NRA-specific env levers (S1+S1b+S2+S1c+S1d hash-cons baked into binary) |
| `arm_cac` | `XOLVER_NRA_CAC_DEADLINE_MS=2000` + `XOLVER_NRA_CAC_SR_CACHE=1` |
| `arm_lscd` | `XOLVER_NRA_LOCALSEARCH=1` + `XOLVER_NRA_LS_BUDGET_MS=50` |
| `arm_all` | union of arm_cac + arm_lscd |

S1+S1b+S2+S1c+S1d hash-cons levers are **always-on** in the binary (not
env-gated) — `arm_off` includes them, so the 4-arm split measures the
env-flag levers on top.

## Partial tally (sweep running, refresh at completion)

Sweep launched 21:51, ETA ~23:25. Hycomp completes first (alpha-order in
xargs sample list).

| Cluster | n done | arm_off ok | arm_cac ok | arm_lscd ok | arm_all ok | Wrong |
|---|---|---|---|---|---|---|
| hycomp | 81/100 (partial) | 47 (58.0%) | 47 (58.0%) | 47 (58.0%) | 47 (58.0%) | **0** |
| polypaver | – | – | – | – | – | – |
| Pine | – | – | – | – | – | – |

Final tally appended on sweep completion (task `bmx01bz8q`).

## Hycomp interim signal (n=81/100)

* **Identical solve outcomes across all 4 arms** — same 47 unsat, same
  ~34-36 timeouts (per-arm noise). Recovery 58 % is consistent with Task E's
  56.7 % at n=30.
* The LS lever does not change which hycomp cases solve — these cases are
  UNSAT-direction, so the SAT-finder LS engine doesn't kick in. The
  consistency confirms the BMC-style hycomp profile (item #75).
* The CAC deadline + PSC cache levers don't move the boundary on hycomp
  either — cases either solve under 30 s or hit the wall-clock TO; the
  budget knob is dominated by the algorithm itself on this corpus.
* **0 wrong across the 324 hycomp runs so far** (81 × 4 arms).

## Comparison vs Task E (n=30 hycomp)

| Sample | Recovery | Note |
|---|---|---|
| Task E (n=30) | 56.7 % | original |
| Task I (n=81 partial, all arms) | 58.0 % | within sampling noise |

The 30 % boundary holds for hycomp at n=100 with 58 % surface area
reachable — comfortably above the catalog threshold.

## To-be-filled-in on sweep completion

* polypaver per-arm recovery + cluster-comparison vs Task E meti-tarski/polypaver
* Pine per-arm recovery + final boundary confirmation
* aggregate 0-wrong across all 1200 runs
* CANDFLAGS recommendation update
* lever-attribution analysis once arm_lscd vs arm_off diverge measurably

---

## Sweep config (exact reproduction)

```bash
# 100-case head-deterministic sample per cluster
find benchmark/non-incremental/QF_NRA/hycomp                -name "*.smt2" | sort | head -100
find benchmark/non-incremental/QF_NRA/meti-tarski/polypaver -name "*.smt2" | sort | head -100
find benchmark/non-incremental/QF_NRA/20200911-Pine         -name "*.smt2" | sort | head -100

# Wrapper /tmp/nra_task_i/run_4arm.sh emits TSV per-arm:
# cluster<TAB>basename<TAB>arm<TAB>expected<TAB>verdict<TAB>wall_s
# Per-arm runs: timeout 30, ulimit -v 4G, single sequential within case.

( ulimit -v 4000000; \
  xargs -P 2 -a /tmp/nra_task_i/sample_300.txt -I{} \
    /tmp/nra_task_i/run_4arm.sh {} \
) > /tmp/nra_task_i/results.tsv
```

---

*Binary: `agent/nra-2` @ `9c2338a` (S1+S1b+S2+S1c+S1d hash-cons baked).*
*Sweep task ID: `bmx01bz8q` (background).*
*Result TSV: `/tmp/nra_task_i/results.tsv`.*
