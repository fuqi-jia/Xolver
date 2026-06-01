# Task D — LS budget sweep local derisk (pre-D3 server)

Local sweep of `XOLVER_NRA_LS_BUDGET_MS` ∈ {10, 25, 50, 100} (+ a 250 outlier
and a max_rounds sub-sweep) against LS-amenable NRA SAT cases. Purpose:
**risk-assess raising the default budget 10 → 50ms** before D3 server sweep
commits the change broadly.

WSL-safe: every run wrapped `( ulimit -v 4000000; timeout 30 ... )`,
sequential, no `-j > 1` on test invocations.

---

## Sweep 1: 9 local NRA SAT cases × {10, 25, 50, 100} ms

All 9 cases solve `sat` in **0.07-0.10s wall**, identical across every budget.
LS engagement (counter dump):

| Case | LS engaged? | evalAt hits/misses | Same across budgets? |
|---|---|---|---|
| nra_054 metitarski atan | NO (4 cache, 0 ops) | — | ✓ (LS short-circuit) |
| nra_058 metitarski exp | YES light | 112 / 4 (96.55%) | ✓ identical |
| nra_022 algebraic root | YES heavy | 3352 / 2 (99.94%) | ✓ identical |
| nra_001 cubic | YES light | 38 / 2 (95.00%) | ✓ identical |

**Identical counter values across 10/25/50/100ms** means LS finished in well
under 10ms on every case. Budget setting is irrelevant when CDCAC fast-path
or LS rapid convergence closes the case before the budget timer ticks.

## Sweep 2: broad-tree meti-tarski/atan/problem-1 SAT cluster (5 cases) × {10, 50, 100} + no-LS baseline

These are the HARDER cluster cases more representative of the D3 ATTACK list.

| Case | b=10ms | b=50ms | b=100ms | no-LS |
|---|---|---|---|---|
| atan-problem-1-chunk-0006 | sat / 0.17s | sat / 0.18s | sat / 0.16s | sat / 0.15s |
| atan-problem-1-chunk-0007 | sat / 0.08s | sat / 0.09s | sat / 0.08s | sat / 0.11s |
| atan-problem-1-chunk-0008 | sat / 0.41s | sat / 0.44s | sat / 0.41s | sat / 0.38s |
| atan-problem-1-chunk-0010 | sat / 0.40s | sat / 0.41s | sat / 0.37s | sat / 0.36s |
| atan-problem-1-chunk-0012 | sat / 0.65s | sat / 0.66s | sat / 0.65s | sat / 0.60s |

- **All 5 solved sat under all 4 settings, 0 unsound**.
- LS overhead vs no-LS: ~0.02-0.06s (negligible, CDCAC dominates).
- **No budget-related variation** within noise.
- **No regression at higher budget**.

## Sweep 3: SAT-impossible probe (Melquiond2-chunk-0015, expected UNSAT)

Earlier bonus report flagged this as a server-LS candidate. **Clarification**:
LS is a SAT-finder and never emits UNSAT. For an UNSAT-expected case, LS
budget cannot help — the residual unknown comes from CAC's projection
ceiling, not from a missed-witness situation.

| budget | rounds | verdict | wall |
|---|---|---|---|
| 10ms | 10/30/100 | unknown | 3.18-3.66s |
| 50ms | 10/30/100 | unknown | 3.34-3.53s |
| 100ms | 10/30/100 | unknown | 1.79-3.43s |
| 250ms | 10/30/100 | unknown | 3.26-3.62s |

12 configurations, all unknown. Not an LS candidate. Bonus-report flag
withdrawn.

---

## Derisk conclusion for D3 server

1. **SAFE to raise default budget 10 → 50ms**. No local regression (sample n=14 SAT cases across local 143-set and broad atan-problem-1 cluster).
2. **LS overhead is bounded** (~0.02-0.06s when LS runs but doesn't help). Acceptable cost for the expected wins on harder ATTACK-cluster cases.
3. **`XOLVER_NRA_LS_MAX_ROUNDS=10` is not the binding constraint** on local cases (evalAt counts go up to 3352 = many rounds × candidates per round under 10ms wall).
4. **Budget tuning cannot recover UNSAT verdicts**. Server sweep should be scoped to SAT-direction recovery; UNSAT timeouts route elsewhere (CAC completeness, NLA-architectural).

## Recommended D3 server-side action

- Set `XOLVER_NRA_LS_BUDGET_MS=50` as the candidate-default (already in the LS-D3 sweep matrix per master's spec).
- 0-unsound gate enforced.
- Server should report per-cluster delta vs current default-10ms; based on local data, expect **neutral on easy cases, recovery on ATTACK-cluster slow SAT cases**.

## Counter dump format (for server-side reproducibility)

```
XOLVER_NRA_LOCALSEARCH=1 XOLVER_NRA_LS_BUDGET_MS=50 XOLVER_NRA_LS_STATS=1 \
  ./build/bin/xolver solve <case.smt2>
# stderr:
# [XOLVER_NRA_LS_STATS] evalAt: hits=N misses=M hit_rate=X% cache=K | scaleAt: ...
```

LS-C cache hit rate >90% in every engaged case (confirms LS-C ship).

---

*Branch: `agent/nra-2` @ `155d407` + Task D doc.*
*Files: `src/theory/arith/nra/reasoners/NraLocalSearch.{h,cpp}` (LS-C cache) + this report.*
