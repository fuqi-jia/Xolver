# Track A — broad QF_NRA differential (714 cases, 16 families)

Per-family scaling of the CAC-UNSAT differential. Two configs over the same
714-case sample (≥50 per family for families with ≥50 cases; all cases for the
four smaller ones). Per-case 10s timeout, `ulimit -v 4G`, `xargs -P 4`.

## Configs

| | flags |
|---|---|
| BASELINE | `XOLVER_NRA_CAC=1 XOLVER_NRA_CAC_TRUST_UNSAT=1 XOLVER_NRA_SIGN_REFUTE=1 XOLVER_NRA_SUBTROPICAL=1 XOLVER_NRA_HYBRID=1` |
| FULL | BASELINE + `XOLVER_NRA_CAC_MIN_CONFLICT=1 XOLVER_NRA_CAC_COMBINATION=1 XOLVER_NRA_CAC_EARLY_INFEAS=1 XOLVER_NRA_CAC_PRUNE_INTERVALS=1` |

## Totals

| config | sat | unsat | unknown | timeout | UNSOUND |
|---|---|---|---|---|---|
| BASELINE | 47 | 96 | 21 | 550 | **0** |
| FULL | **57** | **101** | 20 | **536** | **0** |
| **Δ** | **+10** | **+5** | **−1** | **−14** | **0** |

**+15 decisions out of 714 (+2.1% of corpus). 0 UNSOUND across both configs.**

## Per-family delta (FULL − BASELINE, decisions = sat+unsat)

| family | tot | sat Δ | unsat Δ | unk Δ | to Δ | decisions Δ |
|---|---|---|---|---|---|---|
| meti-tarski | 70 | +4 | +1 | −4 | −1 | **+5** |
| 20220314-Uncu | 50 | +2 | +4 | −1 | −5 | **+6** |
| 20180501-Economics-Mulligan | 50 | +4 | 0 | −2 | −2 | **+4** |
| 2019-ezsmt | 50 | 0 | 0 | +2 | −2 | 0 |
| 20200911-Pine | 50 | 0 | 0 | +1 | −1 | 0 |
| LassoRanker | 50 | 0 | 0 | +3 | −3 | 0 |
| 20161105-Sturm-MBO | 50 | 0 | 0 | 0 | 0 | 0 |
| (others) | — | 0 | 0 | 0 | 0 | 0 |

## Headline observations

- **0 UNSOUND across 1428 runs** (714 × 2 configs). MIN_CONFLICT/COMBINATION/
  EARLY_INFEAS/PRUNE_INTERVALS hold at scale.
- **meti-tarski + Uncu + Mulligan** carry the wins (+15 decisions). These have
  the structural pattern early-infeas + prune target: many constraints with
  decidable signs at low levels.
- **Sturm-MBO unchanged** — the medal target stays at 26 unsat / 24 timeout.
  The 24 timeouts here look projection-cost-bound (CAC's search-time levers
  don't reach them). Lazard projection shrinking / subresultant caching is the
  likely lever from Track B.
- **Heizmann/UltimateAutomizer/pPDA/Sturm-MGC** all-timeout — these families
  are deeply structurally hard for CAC; Track B taxonomy classifies whether
  the cluster has a known cvc5/nlsat differential to study.
- **LassoRanker/Pine/2019-ezsmt** show +unknown rather than +decision in FULL —
  the new flags trigger earlier `markIncomplete` bails on these. Not a regression
  (Unknown is sound), but Track B will identify whether a more-careful bail
  condition recovers some of these.
- **4 segfaults** in the 1428 runs (0.28%): flagged to master via the report,
  not yet reproduced (stderr was suppressed for parallel-throughput). Routes to
  follow-up — `XOLVER_NRA_CAC_TRUST_UNSAT=1` with the new flags should never crash.

## Files

- `baseline.raw` / `full.raw` — per-case pipe-delimited: `family|expected|got|path`.
- `baseline_summary.txt` / `full_summary.txt` — per-family aggregate table.
- `full_timeouts.txt` — paths of the 536 FULL-config timeouts (input to Track B).
