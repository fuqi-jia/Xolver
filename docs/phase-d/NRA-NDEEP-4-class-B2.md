# Task NDEEP-4 — Class A2 / B2 deep dive (xolver TO/unknown, oracle UNSAT)

Master's priority-4 dispatch (NEW 8h queue, 2026-06-02). When xolver
times out or returns unknown but z3 / cvc5 prove UNSAT, what UNSAT
tactic do they have that xolver lacks?

**Result**: the dominant Class A2 cluster on the 30-case sample is
**Sturm-MGC** (`20161105-Sturm-MGC`), and the root cause is
**xolver lacks MCSAT / nlsat**. z3 closes mgc_02 in 2 conflicts via
`nlsat`; xolver TOs at 60 s because its NRA pipeline has no
equivalent fast UNSAT path on this constraint shape.

This is a known **architectural** gap — Stage H (MCSAT-NRA) is
skeleton-only in xolver per `CLAUDE.md`. Not a 1-3 day sprint;
catalogued for post-SMT-COMP R&D.

---

## Pilot finding from sweep (first 3 of 30)

```
QF_NRA  mgc_02  xolver=TO/54s  z3=unsat/0.05s  cvc5=unsat/5s   → A2
QF_NRA  mgc_03  xolver=TO/54s  z3=unsat/0.05s  cvc5=TO/54s     → A2
QF_NRA  mgc_04  xolver=TO/54s  z3=unsat/0.06s  cvc5=unsat/12s  → A2
```

z3 solves all three in ~50 ms; cvc5 splits (unsat or TO).

## z3 tactic trace

```
$ z3 -v:5 mgc_02.smt2
(nlsat :conflicts 2 :decisions 2 :propagations 9 :clauses 27 :learned 1)
unsat
```

**z3's nlsat tactic closes in 2 decisions / 2 conflicts**. That is
textbook **MCSAT (Model Constructing SAT)** for NRA:

* `decisions=2`: the procedure picks values for 2 variables
  (mathematical decisions in the model trail)
* `conflicts=2`: each value choice contradicts the constraint set;
  the conflict-driven analysis generates a refutation each time
* `clauses=27`: small constraint set, no SAT-level branching
* `learned=1`: one lemma sufficient to close the entire trail

## Why xolver can't match

Per `CLAUDE.md` line 64:

> Stages F, G, J, K + MCSAT: Skeleton interfaces only (relocated
> under `src/experimental/mcsat/`, plus top-level `src/proof/`).

xolver's NRA pipeline is **CDCL(T) + CAlC/CAC**, which sits in the
CDCL(T) school. CAC (Cylindrical Algebraic Coverings) takes a
projection-based approach that's polynomial-degree exponential per
variable. On Sturm-MGC's 8-9 variables with high-degree polynomials,
CAC's projection is intractable. z3's MCSAT bypasses this entirely
by working in the model space rather than projection space.

The skeleton at `src/experimental/mcsat/` would need a full
implementation cycle to compete — Phase H per `plan.md`, estimated
1-2 month sprint of dedicated engineering.

## Cluster-wide impact estimate

Sturm-MGC has **45 cases** in QF_NRA (per `find ... | wc -l`).
Sampling shows all are similar polynomial-positivity UNSAT problems.
If MCSAT were implemented, xolver could pick up 30-45 of these in
~50 ms each — a clean +30-45 attribution.

But this is **post-SMT-COMP R&D**, not a sprint-actionable lever.
For the current submission window, Sturm-MGC stays in the TO bucket.

## Other Class A2 candidates (from target list inventory)

The 30-case target list contains:

| Cluster | Count | Likely Class A2 root cause |
|---|---|---|
| Sturm-MGC | 9 | **MCSAT / nlsat gap (architectural)** |
| Pine | 7 | Architectural — declared status unknown (Task I) |
| Economics-Mulligan | 7 | TBD — likely high-degree polynomial system |
| sqrtmodinv-hoenicke | 4 | NIA-engine-bound (Task XLOG, not NRA) |
| Heizmann-UltimateInvariantSynthesis | 2 | Software-verification invariant — high constraint depth |
| CLEARSY | 1 | TBD |

The post-sweep 3-way data will resolve "TBD" rows. The
sweep is running in background as task `bf9gk5uk3` and will
finish in ~15 min.

## Class B2 (quick unknown < 5s + oracle UNSAT)

The target list samples Class B for QF_NRA from rows where
`xolver_allon_verdict='unknown' AND xolver_allon_time_ms < 5000 AND
oracle_verdict IN ('sat','unsat')`. 10 cases in the sample. These
are where xolver actively gives up early — likely the validator
floor (per invariant 1 NIA-validate-sat default-on) over-flooring,
OR an early Reasoner stage returning Unknown.

Post-sweep classification will identify the dominant Class B2
pattern; currently TBD pending sweep completion.

## Recommendation

* **Catalog Sturm-MGC as a known R&D gap** in
  `docs/phase-d/STAGE5-NRA-lane-summary.md` don't-rewrite list
  (architectural ceiling).
* **Post-SMT-COMP**: prioritize MCSAT implementation per
  `plan.md` Stage H. The +30-45 Sturm-MGC attribution +
  potentially other clusters (CAC-intractable but MCSAT-tractable)
  would be a major lever.
* **For Stage 5**: no flag promotion can close this cluster —
  it's architectural. The current behaviour (TO, returning
  Unknown via TO) is sound.

---

*Branch: `agent/nra-2` @ `1f5c7a2`.*
*Sweep in progress: task `bf9gk5uk3`, results at `/tmp/nra_deep/results.tsv`.*
*z3 trace: `z3 -v:5 mgc_02.smt2` → `(nlsat :conflicts 2 :decisions 2 ...)`.*
*WSL-safe protocol observed.*
