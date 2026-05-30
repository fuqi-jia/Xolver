# QF_UFNRA -5 FFT family ablation

Master added a tasklet: single-point identify whether
`XOLVER_NRA_CAC_TRUST_UNSAT` (soundness-gated) or
`XOLVER_NRA_CAC_DEADLINE_MS=2000` is the culprit for the panda baseline's
`-5` on the FFT family.

## Method

Three configs over the full 58-case QF_UFNRA corpus (and again FFT-only at
60s per case):

  | config | flags |
  |---|---|
  | `allon` | full bundle + `TRUST_UNSAT=1` (default deadline 2000ms) |
  | `no_trust` | full bundle MINUS `TRUST_UNSAT` |
  | `deadline60s` | full bundle + `TRUST_UNSAT=1` + `DEADLINE_MS=60000` |

Full bundle = `XOLVER_NRA_CAC + SIGN_REFUTE + SUBTROPICAL + HYBRID +
MIN_CONFLICT + COMBINATION + EARLY_INFEAS + PRUNE_INTERVALS`. xargs -P 4,
`ulimit -v 4G`. Two budgets: 10s/case (full UFNRA) and 60s/case (FFT only).

## Results at 10s/case (full 58 UFNRA)

| config | FFT decided | sqrtmodinv unknown | sqrtmodinv to | cas to | 0004 to |
|---|---|---|---|---|---|
| allon | 1 (1 unsat) | 19 | 2 | 26 | 1 |
| no_trust | 1 (1 unsat) | 19 | 2 | 26 | 1 |
| deadline60s | 1 (1 unsat) | 19 | 2 | 26 | 1 |

**All three configs IDENTICAL.** UNSOUND=0 in all.

## Results at 60s/case (FFT only)

| config | sat | unsat | timeout | UNSOUND |
|---|---|---|---|---|
| allon | 1 | 9 | 0 | 0 |
| no_trust | 1 | 9 | 0 | 0 |
| deadline60s | 1 | 9 | 0 | 0 |

**All three configs solve 10/10 at 60s.**

## Conclusion

At 10s wall: only 1 FFT case decided regardless of flag choice. At 60s wall:
all 10 decided regardless. **Neither TRUST_UNSAT nor DEADLINE_MS=60000 vs
=2000 changes anything at these local budgets.**

The panda's -5 is not reproducible locally at 10s or 60s. Hypotheses:
- Panda uses a per-case budget BETWEEN 10s and 60s where DEADLINE_MS=2000
  causes CAC to bail before any FFT case completes, while
  DEADLINE_MS=60000 lets CAC finish at least 5 more cases.
- Or the -5 is vs a non-CAC baseline (no `XOLVER_NRA_CAC=1` at all),
  meaning CAC itself is hurting FFT — needs the FFT-without-CAC config to
  test.
- Or panda runs without `_ONLY` so Collins-fallback time also matters.

Master decides next step.
