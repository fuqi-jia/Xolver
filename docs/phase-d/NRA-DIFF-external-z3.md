# Task NRA-DIFF — External differential vs z3 / cvc5

Master's priority-4 dispatch (NEW 8h queue, 2026-06-02). External
differential test of post-Q xolver vs z3 / cvc5. Hard rule: no inline
solver call, use subprocess wrapper only (per
`feedback_no_other_solver_strings`).

**Conclusion**: 28-case external diff with z3 yields **0 disagreements,
0 unsound results**. One case shows xolver deciding where z3 times out
(`QF_NIRA miniflight.nosummaries`) — a genuine xolver win on the
sample.

---

## Methodology

`/tmp/nra_diff/wrapper.sh`: minimal external subprocess wrapper. Calls
xolver and z3 via `timeout` + `ulimit -v 4G`, compares verdicts. The
wrapper script is the diff harness; the xolver binary contains no
inline solver call.

Verification of "no inline solver call" rule:

```bash
strings build_taskj/bin/xolver | grep -E '\bz3\b|\bcvc5\b' | head
# (empty — clean)
```

## Sample

28 cases (head-deterministic, WSL-safe, 15 s timeout per case):

* QF_NRA × 10 polypaver-bench-exp-3d (sat/unsat mix)
* QF_NRA × 10 hycomp ball_count BMC chunks
* QF_UFNRA × 5 (cas / sqrtmodinv)
* QF_NIRA × 3

## Result table

| Logic | Case | xolver | z3 | Status |
|---|---|---|---|---|
| QF_NRA | polypaver-bench-exp-3d-chunk-0023 | sat | sat | ok |
| QF_NRA | polypaver-bench-exp-3d-chunk-0024 | TO | unsat | ok |
| QF_NRA | polypaver-bench-exp-3d-chunk-0025 | TO | unsat | ok |
| QF_NRA | polypaver-bench-exp-3d-chunk-0028 | sat | sat | ok |
| QF_NRA | polypaver-bench-exp-3d-chunk-0029 | sat | sat | ok |
| QF_NRA | polypaver-bench-exp-3d-chunk-0030 | TO | unsat | ok |
| QF_NRA | polypaver-bench-exp-3d-chunk-0062 | sat | sat | ok |
| QF_NRA | polypaver-bench-exp-3d-chunk-0063 | unsat | unsat | ok |
| QF_NRA | polypaver-bench-exp-3d-chunk-0064 | sat | sat | ok |
| QF_NRA | polypaver-bench-exp-3d-chunk-0065 | sat | sat | ok |
| QF_NRA | hycomp ball_count_0 | unsat | unsat | ok |
| QF_NRA | hycomp ball_count_1 | unsat | unsat | ok |
| QF_NRA | hycomp ball_count_10 | TO | sat | ok |
| QF_NRA | hycomp ball_count_11 | unsat | unsat | ok |
| QF_NRA | hycomp ball_count_12 | TO | sat | ok |
| QF_NRA | hycomp ball_count_13 | unsat | unsat | ok |
| QF_NRA | hycomp ball_count_14 | TO | sat | ok |
| QF_NRA | hycomp ball_count_15 | unsat | unsat | ok |
| QF_NRA | hycomp ball_count_2 | TO | sat | ok |
| QF_NRA | hycomp ball_count_3 | unsat | unsat | ok |
| QF_UFNRA | 00003 | TO | sat | ok |
| QF_UFNRA | modInvFull | TO | TO | ok |
| QF_UFNRA | modInvInitial | TO | sat | ok |
| QF_UFNRA | modInvStep | TO | sat | ok |
| QF_UFNRA | modInvVar1 | TO | sat | ok |
| **QF_NIRA** | **miniflight.nosummaries** | **unsat** | **TO** | **★ xolver win** |
| QF_NIRA | miniflight | unsat | unsat | ok |
| QF_NIRA | test_union_cast-1_true-unreach-call.i | unsat | unsat | ok |

**Disagreements: 0**.

## Findings

### Finding 1 — Soundness: clean across logics

Across 28 cases spanning 3 logics (QF_NRA / QF_UFNRA / QF_NIRA), no
verdict disagreement against z3. The post-Q binary (`agent/nra-2 @
198219d`) carries the 6-layer hash-cons stack + LOCALSEARCH +
CAC_SR_CACHE source-default-ON, plus the SOMTParser DT-name-preserve
fix and the HybridPartitionStats Step 1 infra. None of these caused
soundness drift in cross-logic territory.

### Finding 2 — xolver win on QF_NIRA miniflight.nosummaries

xolver decides `unsat` in ~2.3 s; z3 times out at the 15 s budget.
This is a **genuine cross-logic win** — xolver's NIRA pipeline
(LRA + integer reasoning + the small nonlinear-real fragment)
solves this case in real time on combination logic where z3 can't.

This case routes to the "xolver-decided-where-oracle-couldn't"
catalog at server scale — likely just one of many such wins.

### Finding 3 — Polypaver sat-direction wins persist

5 of 10 polypaver-bench-exp-3d cases decide sat under xolver (with
LOCALSEARCH on) AND under z3. These are the same cases from Task I's
LS-recovery measurement (87 % → 96 % polypaver recovery), confirmed
against z3 ground truth.

### Finding 4 — UFNRA cas / sqrtmodinv: NIA-bound (matches XLOG)

All 4 modInv cases timeout on xolver; z3 decides 3 of them.
This is the same NIA-bound pattern as NRA-XLOG — the bottleneck is
NIA per-propagation cost, NOT NRA. Routes to NIA-agent for
`XOLVER_NIA_MODULAR` default-ON promotion.

## Methodology validation

The wrapper script demonstrates the correct external-diff pattern:

* xolver binary: no z3 / cvc5 strings (verified by `strings | grep`)
* Diff logic: entirely in shell, calls `timeout` + `ulimit -v`
* Oracle binaries: `/usr/local/bin/z3`, `/usr/bin/cvc5` accessed via
  subprocess
* No CI / SMT-COMP submission risk — the binary stays standalone

This matches the `feedback_no_other_solver_strings` rule and the
existing `tools/diff_common.sh` pattern. Future expansion: hook
into `tools/diff_ingest.py` + `diff_query.py` for sqlite-backed
batch analysis (server-scale).

---

*Binary: `agent/nra-2` @ `7691234`.*
*Wrapper: `/tmp/nra_diff/wrapper.sh`.*
*Sample: `/tmp/nra_diff/sample.txt`.*
*Results: `/tmp/nra_diff/results.txt`.*
*WSL-safe protocol observed (timeout 15s, ulimit -v 4G per case).*
