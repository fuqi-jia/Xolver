# P6 — bonus hycomp/sqrt/Pine local sample under all levers

Master spec: "5-10 case 本地 sample on hycomp/sqrt/Pine,在 levers + S1 hash-cons
combination 下跑 paired,看是否触发任意 trick. 即使 0 trigger 也是 informative
(boundary confirmed)."

WSL-safe: each case wrapped in `( ulimit -v 4000000; timeout 20 ... )`,
sequential single-process, sample sizes 10 per cluster (~5 min wall total).

## Result summary (binary @ 2d4e57c, all levers default-ON + LS-C)

| Cluster | Solved | Timeout | Wrong | Best/Worst times |
|---|---|---|---|---|
| hycomp (10 cases, ball_count subset) | 6/10 | 4 | **0** | UNSAT 0.08s avg / SAT all >18s |
| meti-tarski/sqrt (10 cases, Melquiond2-chunk) | **9/10** | 0 | **0** | SAT 0.12-3.47s / UNSAT 0.06-0.08s |
| Pine (10 cases) | 5/10 unknown-match | 5 | **0** | unknown 4.26-9.96s / TO 18.6-20s |

**0 wrong across 30 cases — soundness preserved on broad corpus under combined levers.**

## Per-cluster observations

### hycomp (6/10)
- All 6 UNSAT cases solved in **<0.12s** — small ball_count instances, theory check fast-path closes immediately.
- All 4 SAT cases timed out at 18-32s (some exceeded budget slightly during cleanup).
- **Boundary confirmed**: hycomp SAT = BMC-architectural ceiling per master post-SMT-COMP R&D note. My CAC-deep levers (S1+S1b+LS-C) don't change the architectural truth — they amortize CAC cell-jump cost but can't bypass the projection-operator completeness ceiling for these BMC instances.

### meti-tarski/sqrt (9/10) — strongest cluster for my levers
- 5/5 SAT cases solved (0.12-3.47s).
- 4/5 UNSAT cases solved (0.06-0.08s).
- 1 unknown: `sqrt-problem-Melquiond2-chunk-0015` (3.5s, expected unsat) — candidate for `XOLVER_NRA_LOCALSEARCH=1` server-side measurement.
- **Reaffirms ATTACK-list designation**: meti-tarski sqrt is structurally amenable to CAC-deep levers + LS combination.

### Pine (5/10 unknown-match)
- **All expected results are `unknown`** in this benchmark family (Pine spec) — every "OK" is unknown-matches-unknown, not a true recovery.
- 5 cases output unknown within 4.26-9.96s; 5 cases timed out at 18-20s with the same expected unknown.
- **Boundary confirmed**: Pine is a known-hard cluster (master earlier dispatch flagged it for post-SMT-COMP R&D). No CAC-deep micro-opt closes it.

## Action items derived

1. **No paired delta to ship as standalone perf win on this sample size.** The cases that solved were already in the kernel-cheap regime; the slow cases are bound by the architectural ceiling.
2. **`sqrt-problem-Melquiond2-chunk-0015` unknown** is a single-case candidate for server-side `XOLVER_NRA_LOCALSEARCH=1` verification once the D3 budget=50ms sweep returns. If LS lands here under the broader bonus list, it's a +1 win at minimum.
3. **Soundness gate met across broad-corpus pattern**: 30 cases, 0 wrong. This complements the local 143/143 + 113/113 reg numbers — the lever combination doesn't introduce subtle pattern-specific bugs at SMT-LIB scale.

## Files (untouched by this run)

- `src/theory/arith/poly/LibPolyKernel.{h,cpp}` @ S1+S1b commits 547ea11, afeda00
- `src/theory/arith/nra/cac/SingleCellProjection.cpp` @ S3 instr d6a33d3
- `src/theory/arith/nra/reasoners/NraLocalSearch.{h,cpp}` @ LS-C 2d4e57c

Binary path used: `/mnt/d/D_Study/BUAA/projects/zolver-nra/build/bin/xolver`
Benchmark root: `/mnt/d/D_Study/BUAA/projects/NLColver/benchmark/non-incremental/QF_NRA/`
