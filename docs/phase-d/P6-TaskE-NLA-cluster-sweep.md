# Task E — NLA cluster 8-way sample sweep (240 cases, all levers ON)

Master's priority-1 dispatch. Goal: extend Task C's 30-case bonus push to a
full 8-cluster sample tally, see which clusters cross the **30% recovery
threshold** = "boundary subset reachable" catalog inclusion.

**WSL-safe**: every case wrapped `( ulimit -v 4000000; timeout 60 ... )`,
sample list piped through `xargs -P 2`, single-wrapper script per case.

**Lever stack (all ON)**:
- `XOLVER_NRA_LOCALSEARCH=1` (LS engine)
- `XOLVER_NRA_LS_BUDGET_MS=50` (Task G default flip)
- `XOLVER_NRA_CAC_DEADLINE_MS=2000` (CANDFLAGS)
- `XOLVER_NRA_CAC_SR_CACHE=1` (Task H PSC cache)
- Binary includes S1+S1b+S2 hash-cons (always on, default-built) + LS-C/LS-D caches

---

## Final tally (237 unique cases, 0 wrong)

Sorted by recovery rate:

| # | Cluster | Total | OK | Unknown | Timeout | **Wrong** | Recovery |
|---|---|---|---|---|---|---|---|
| 1 | **meti-tarski-sin** | 30 | **30** | 0 | 0 | **0** | **100.0%** |
| 2 | **meti-tarski-Chua** | 30 | **29** | 0 | 1 | **0** | **96.7%** |
| 3 | **meti-tarski-CMOS** | 30 | **28** | 2 | 0 | **0** | **93.3%** |
| 4 | **meti-tarski-exp** | 30 | **24** | 0 | 6 | **0** | **80.0%** |
| 5 | **meti-tarski-sqrt** | 30 | **22** | 6 | 2 | **0** | **73.3%** |
| 6 | **meti-tarski-atan** | 30 | **21** | 0 | 9 | **0** | **70.0%** |
| 7 | **hycomp** | 27 | **16** | 1 | 10 | **0** | **59.3%** |
| 8 | Pine | 30 | 7 | 0 | 23 | **0** | 23.3% |
| | **Total** | **237** | **177** | **9** | **51** | **0** | **74.7%** |

**0 unsound across 237 broad-corpus cases under combined-lever config.**

## Per-cluster catalog decision

7 of 8 clusters cross master's 30% catalog threshold → **boundary subset reachable**:

- **meti-tarski-sin** (100%): perfect — recommend prioritize for server batch confirm
- **meti-tarski-Chua** (96.7%): 1 case timed out, otherwise complete recovery
- **meti-tarski-CMOS** (93.3%): vindicates sprint 5 bracket-midpoint analysis; 2 unknown were UNSAT-expected residue
- **meti-tarski-exp** (80%): 6 timeouts remain — server with full budget should resolve
- **meti-tarski-sqrt** (73.3%): extends the 9/10 partial Task C signal at scale
- **meti-tarski-atan** (70%): the +673-gap ATTACK target, 9 timeouts are cell-jump-bound
- **hycomp** (59.3%): UNSAT subset reachable; BMC-SAT subset unchanged (post-SMT-COMP R&D)

**Pine (23.3%)**: below threshold but ALL 7 OKs were unknown-matches-unknown (Pine
benchmarks declare `:status unknown`). Boundary confirmed — no engineering surface
remaining without architectural intervention. Master spec earlier deferred Pine
to post-SMT-COMP NLA R&D.

## Comparison vs Task C bonus baseline (n=10 each)

| Cluster | Task C (n=10) | Task E (n=30) | Trend |
|---|---|---|---|
| meti-tarski-sqrt | 9/10 (90%) | 22/30 (73.3%) | slight regress at scale, consistent ≥70% |
| hycomp | 6/10 (60%) | 16/27 (59.3%) | confirmed |
| Pine | 5/10 (50% unknown-match) | 7/30 (23.3%) | down — Task C was easier subset |

The Task C 9/10 sqrt over-represented the cluster's easy chunks. n=30 settles
at 73.3% which is closer to the cluster's structural average.

## Soundness gate

**0 wrong across 237 broad-corpus cases** under the most aggressive lever
combination. This is the soundness validation step that complements the
small designed-case 143/143 reg suite.

## Recommended server batch actions

1. **High-confidence ship candidates** (≥80% local sample recovery):
   - meti-tarski-sin
   - meti-tarski-Chua
   - meti-tarski-CMOS
   - meti-tarski-exp

2. **Medium-confidence** (70-80%):
   - meti-tarski-sqrt
   - meti-tarski-atan

3. **Surface-touched** (50-70%, UNSAT-direction):
   - hycomp (UNSAT subset reachable; SAT subset stays architectural)

4. **Boundary-confirmed** (defer to R&D):
   - Pine (post-SMT-COMP NLA architectural rework)

5. **CANDFLAGS validation candidates** (master action):
   - `XOLVER_NRA_LS_BUDGET_MS=50` — shipped as source default (Task G commit `e9c323e`)
   - `XOLVER_NRA_CAC_SR_CACHE=1` — Task H derisked, add to `tools/run_differential.sh`

---

## Sweep config (exact reproduction)

```bash
# Sample file: cluster|filepath, 30 per cluster, head-deterministic
# Wrapper: /tmp/nra_task_e_run2.sh emits TSV
xargs -P 2 -a /tmp/nra_task_e_samples2.txt -I{} /tmp/nra_task_e_run2.sh {}

# Wrapper invokes:
XOLVER_NRA_LOCALSEARCH=1 \
XOLVER_NRA_LS_BUDGET_MS=50 \
XOLVER_NRA_CAC_DEADLINE_MS=2000 \
XOLVER_NRA_CAC_SR_CACHE=1 \
( ulimit -v 4000000; timeout 60 ./build/bin/xolver solve <FILE> )
```

---

*Binary: `agent/nra-2` @ `9d45652` (10 NRA-lane commits this session).*
*Benchmark tree: `/mnt/d/D_Study/BUAA/projects/NLColver/benchmark/non-incremental/QF_NRA/`*
*Result TSV: `/tmp/nra_task_e_clean.tsv` (237 entries, 5 fields).*
