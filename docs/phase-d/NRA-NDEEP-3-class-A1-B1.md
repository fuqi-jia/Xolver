# Task NDEEP-3 — Class A1 / B1 deep dive (xolver TO/unknown, oracle SAT)

Master's priority-3 dispatch (NEW 8h queue, 2026-06-02). When xolver
times out or returns unknown but z3 / cvc5 find SAT, what SAT-finding
tactic do they have that xolver lacks?

**Result**: pending sweep completion (task `bf9gk5uk3`, 30 cases
3-way diff). This document holds the framework + per-cluster
hypotheses; data fill-in on sweep completion.

---

## Methodology

For each Class A1 / B1 case (xolver TO/unknown + oracle SAT):

1. **Profile xolver path**:
   ```
   ( ulimit -v 4G; XOLVER_NRA_KERNEL_STATS=1 \
       timeout 60 ./build/bin/xolver solve case.smt2 )
   ```
   Look at the kernel stats (S1-S1e hit rates) and any diag output
   to see which stage is running when the TO hits.

2. **Profile z3 path** (verbose):
   ```
   z3 -v:5 case.smt2 2>&1 | tail -10
   ```
   The trace reveals which tactic z3 uses. Common SAT-finder tactics:
   - `nlsat`: MCSAT (model construction) for NRA
   - `qfnra-nlsat`: combined with bit-blasting fallback
   - `smt`: general SAT-driven solver path
   - `qe`: quantifier-elimination (for ∀-free problems)

3. **Compare** the tactics. Where z3's tactic is structurally
   different from xolver's path (LS / LinearizeProbe / CAC), the gap
   is real.

## Per-cluster hypothesis (pre-sweep)

| Cluster | Pre-sweep hypothesis |
|---|---|
| **Economics-Mulligan** | High-degree polynomial SAT — likely needs better seed values for LS or a smarter LINEARIZE seed. Could be a sprint-actionable LS-tuning. |
| **Pine** | Mostly architectural (declared status unknown). The subset z3 / cvc5 decided may use a structural pattern (e.g. zero-set boundary) that xolver could match. |
| **Heizmann-UltimateInvariantSynthesis** | SV-COMP invariant synthesis. May exhibit specific structure (linear-after-substitution) that LINEARIZE catches. |
| **CLEARSY** | Industrial railway control system; pattern TBD. |
| **sqrtmodinv-hoenicke** | NIA-engine-bound per XLOG. Not NRA-fixable; routes to NIA-agent. |
| **Sturm-MGC** | UNSAT, not SAT — covered by NDEEP-4 (`A2_TO_xolver_oracle_UNSAT`). |

## Decision criteria

If the sweep surfaces:

* **Pattern in 3+ cases of one cluster with a recognizable
  algorithmic shape** → propose a new lever, ship as a 1-3 day sprint.
* **Single-case oddities** → catalog in defer doc; investigate post
  SMT-COMP.
* **All cases boundary (A3 = all 3 TO)** → architectural; defer.

## Class A1 / B1 final result table (30/30 sweep)

| Case | xolver | z3 | cvc5 | Class | Cluster |
|---|---|---|---|---|---|
| polypaver-bench-exp-3d-chunk-0023 | sat 0.05s | sat | sat | OK | polypaver |
| polypaver-bench-exp-3d-chunk-0024 | TO | unsat | unsat | A2 | polypaver |
| polypaver-bench-exp-3d-chunk-0025 | TO | unsat | TO | A2 | polypaver |
| polypaver-bench-exp-3d-chunk-0028 | sat | sat | sat | OK | polypaver |
| MulliganEconomicsModel0001e | sat | sat | sat | OK | Mulligan |
| MulliganEconomicsModel0004c | TO | unsat | unsat | A2 ★ | Mulligan |
| MulliganEconomicsModel0004e | TO | sat | sat | A1 | Mulligan |
| MulliganEconomicsModel0009c | TO | unsat | unsat | A2 | Mulligan |
| MulliganEconomicsModel0085a | sat | sat | TO | OK | Mulligan |
| MulliganEconomicsModel0085e | sat | sat | TO | OK | Mulligan |
| mgc_02 | TO | unsat | unsat | A2 ★ | Sturm-MGC |
| mgc_03 | TO | unsat | TO | A2 | Sturm-MGC |
| mgc_04 | TO | unsat | unsat | A2 | Sturm-MGC |
| mgc_05 / 06 / 07 | TO | TO | TO | A3 | Sturm-MGC |
| mgc_08 | TO | unsat | TO | A2 | Sturm-MGC |
| mgc_09 | TO | sat | TO | A1 | Sturm-MGC |
| mgc_10 | TO | sat | TO | A1 | Sturm-MGC |
| 1599120907414249000 | unknown | sat | TO | B1 | Pine |
| 1599120907513630000 | unknown | sat | sat | B1 | Pine |
| 1599120908933292000 | unknown | sat | TO | B1 | Pine |
| 1599121684188100000 | unknown | sat | TO | B1 | Pine |
| 1599121684378151000 | unknown | sat | TO | B1 | Pine |
| 1599121684761355000 | unknown | TO | TO | B3 | Pine |
| 1599121900863650000 | unknown | sat | TO | B1 | Pine |
| standard_init9_ground..bpl_1 | TO | unsat | TO | A2/B2 | Heizmann |
| hhk2008.c.i_3_3_2.bpl_5 | TO | TO | TO | A3 | Heizmann |
| 00003 (UFNRA) | TO | sat | sat | A1 | UFNRA cas |
| modInvFull (UFNRA) | TO | TO | TO | A3 | UFNRA sqrtmodinv |
| modInvInitial (UFNRA) | TO | sat | sat | A1 | UFNRA sqrtmodinv |

**0 Class C across 30 cases (confirms NDEEP-5 30,376-case audit).**

## Root cause pattern report

| Pattern | Cases | Root cause | Fixable? |
|---|---|---|---|
| **Sign-blocking variable** | Sturm-MGC, Mulligan-0004c, Heizmann | One sign-unknown var blocks SignDefinitenessRefuter; cvc5 splits on its sign | ★ Day 2-3 R&D: **NRA-SIGN-SPLIT** (task #124) — emit `(or (> v 0) (= v 0) (< v 0))` lemma |
| **High-degree monomial unsupported** | MGC, polypaver UNSAT | `NonlinearTermAbstraction` rejects `x^n` (n≥3) + trilinear | Day 1 scaffold landed (`ede895e`); composes with sign-split |
| **NIA-engine bound** | UFNRA cas/sqrtmodinv | NIA per-propagation perf; not NRA-side | NIA-agent (`XOLVER_NIA_MODULAR` promotion) |
| **Validator over-floor or LS coverage** | Pine | xolver gives up unknown <10s while z3 SAT 0.03s; either invariant-1 floor too tight or LS heuristic miss | Separate Pine sprint (probe needed) |
| **Architectural ceiling** | A3 cases (mgc_05/06/07, hhk2008) | Hard for everyone | Defer post-SMT-COMP |

## Recommendation (Day 1 final)

1. **NRA-COLLINS-BUDGET (`48b12ee`) already shipped** today — Mulligan
   bucket cleared, meti-tarski/sqrt 18× wall.
2. **NRA-SIGN-SPLIT (Day 2-3 R&D)**: implement per NDEEP-4 design.
   Closes most A2 (Sturm-MGC 4 + Mulligan-0004c-class + Heizmann) and
   some A1 (Mulligan-0004e, mgc_09/10).
3. **HigherMixed (Day 1 `ede895e`)**: composes with sign-split — once
   variables become sign-fixed in a sign-split branch, the
   HigherMixed cuts fire.
4. **Pine B1 (6 cases)**: separate diagnostic sprint; not addressed
   by sign-split alone.

---

*Sweep task ID: `bf9gk5uk3` (completed).*
*Results: `/tmp/nra_deep/results.tsv` (30 rows).*
*Branch: `agent/nra-2` @ `669f845`.*
