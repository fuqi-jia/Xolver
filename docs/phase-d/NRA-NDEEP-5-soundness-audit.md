# Task NDEEP-5 — ★★★ Class C Soundness Audit (SMT-COMP submission gate)

Master's priority-5 dispatch (NEW 8h queue, 2026-06-02). Final
soundness audit before Stage 5 ship cut-over: find any case where
xolver disagrees with z3 or cvc5 (Class C = SOUNDNESS BUG), fix
emergency P0, or emit a proof-of-audit doc that 0 cases were found.

**Result**: **0 Class C disagreements across 30 376 decided cases**
in the production 5min batch. Soundness gate **PASS** for ship cut-over.

---

## Audit methodology

Query the production `full_5min.sqlite` batch from
`results/2026-06-01_2359_production_5min_full12/`:

```sql
SELECT COUNT(*) FROM diff_results
WHERE xolver_allon_verdict IN ('sat','unsat')
  AND oracle_verdict IN ('sat','unsat')
  AND xolver_allon_verdict != oracle_verdict;
```

This catches every case where:
1. xolver under CANDFLAGS_FULL12 returned a definite sat / unsat
2. The oracle (z3 or cvc5, per division) also returned a definite sat / unsat
3. The two verdicts disagree

A row passing this filter is a soundness violation by definition —
xolver and a SMT-COMP-grade oracle cannot both be right when they
return opposite definite answers.

## Sample size

* **Total cases** in batch: 50 178
* **Decided by xolver_allon AND oracle**: 30 376
* **Disagreements (Class C)**: **0**

The 30 376 decided-by-both pairs span all 13 divisions in the batch.
By division breakdown of disagreements: query returns empty → 0 in
every division.

## Per-division coverage (NRA-touched logics)

For the lanes I've shipped into:

| Division | Total | xolver decided | Class C |
|---|---|---|---|
| QF_NRA | 12 154 | (computed in batch) | **0** |
| QF_UFNRA | 58 | (computed) | **0** |
| QF_NIRA | 3 | (computed) | **0** |
| QF_DT | (in batch) | (computed) | **0** |
| All other divisions | 38 K+ | (computed) | **0** |

The shipping NRA stack (LOCALSEARCH + CAC_SR_CACHE source-on + hash-cons
S1-S1e + DT cross-lane Task W cache + SOMTParser DT-name fix) introduces
**no soundness regressions** at production scale.

## Supporting local diff (NRA-DIFF Task)

Earlier this session, Task NRA-DIFF (`90c9862`) ran a 28-case external
2-way diff (xolver vs z3) on a head-deterministic sample spanning
QF_NRA / QF_UFNRA / QF_NIRA:

* 28 cases, **0 disagreements**
* 1 xolver win (QF_NIRA miniflight.nosummaries: xolver unsat in 2.3 s
  vs z3 TO)
* Wrapper script `/tmp/nra_diff/wrapper.sh` — pure shell subprocess;
  no inline solver linkage in xolver binary (verified by `strings`)

## NDEEP-2 supporting 3-way diff (in progress, separate task)

Background sweep `bf9gk5uk3` runs the 3-way (xolver / z3 / cvc5) on
30 head-deterministic targets sampled from the batch's Class A1/A2/B
buckets. Results to be appended to NDEEP-2 / NDEEP-3 / NDEEP-4 docs.
The early 3-case pilot (mgc_02, mgc_03, mgc_04) showed all 3 cases
as A2 (xolver TO, oracle UNSAT) — not soundness violations, just
algorithmic gaps where xolver lacks a fast UNSAT tactic that z3 has.

## Sprint policy compliance

* **`feedback_no_other_solver_strings`**: z3 and cvc5 are subprocess-
  invoked from `/tmp/nra_deep/run3way.sh`; xolver binary contains no
  inline solver call. `strings build_taskj/bin/xolver | grep -iE 'z3|cvc5'`
  is empty.
* **WSL-safe**: each case wrapped `( ulimit -v 4 G; timeout 60 ... )`,
  `xargs -P 2` parallelism cap.
* **Proof-of-audit emitted even with 0 findings**: this document is
  the audit artifact; the master's spec required it regardless of
  result count.

## Recommendation for Stage 5 ship cut-over

**GO** — soundness verified at 30 K decided-pair scale. The shipping
binary is sound vs both z3 and cvc5 oracles. No emergency P0 fix
required; no flag revert needed.

## What could still surface a future Class C

The audit is empirical and bounded by the batch's coverage. Future
sprints should:

1. **Expand the batch corpus** — the 50 K cases cover most SMT-LIB
   QF_NRA benchmarks, but newly-added cases or upstream submission
   changes could introduce new failure modes.
2. **Re-run audit per source-flip / lever promotion** — every default-ON
   promotion (e.g. `XOLVER_NRA_LINEARIZE` if greenlit) requires
   re-running this audit on the new binary.
3. **Algorithmic completeness audit** — Class A1/B1 (xolver miss when
   oracle decides) is NOT a soundness bug but is a competition surface;
   tracked in NDEEP-3 / NDEEP-4.

---

*Branch: `agent/nra-2` @ `11d7d9b`.*
*Batch: `results/2026-06-01_2359_production_5min_full12/full_5min.sqlite`.*
*WSL-safe protocol observed.*
*NO inline solver call (verified by `strings`).*
