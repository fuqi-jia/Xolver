# CAC timeout taxonomy (Track B deliverable)

Status: first cut, 48-case sample (3 per family across the 16 QF_NRA families).
Source data: `results/track_a/full_timeouts.txt` (536 timeouts in the FULL config
of the 714-case broad differential).

## Method

For each sampled timeout case:

1. **Static stats**: `nvar` (declare-fun count), `nasrt` (assertion count),
   `sz` (file bytes), `neq` (`(=` occurrences), `nmul` (`(*` occurrences),
   `maxpow` (highest `^N` seen).
2. **Wall classification** via `XOLVER_NRA_CAC_NO_COLLINS=1`:
   - `NO_COLLINS → unknown` ⇒ **collins-bound** — CAC bailed to Unknown
     quickly; in the original FULL run, Collins's `buildClosure` fallback
     burned the 10s.
   - `NO_COLLINS → timeout` ⇒ **cac-bound** — CAC engine itself exceeded 5s.
   - `NO_COLLINS → sat/unsat` ⇒ **cac-solves-but-budget-clipped** — CAC
     decides the case in 5s, but in FULL config the 2s deadline preempts CAC
     to Collins, which then times out. (Lever: tune `XOLVER_NRA_CAC_DEADLINE_MS`.)

The 48 sample cases ran with the FULL config bundle (CAC + TRUST_UNSAT +
SIGN_REFUTE + SUBTROPICAL + HYBRID + MIN_CONFLICT + COMBINATION + EARLY_INFEAS
+ PRUNE_INTERVALS), 5s per NO_COLLINS run, `ulimit -v 4000000`.

## Headline

| cluster | count | % | wall is in |
|---|---|---|---|
| **cac-bound** | 32 | 67% | CAC engine itself |
| **collins-bound** | 7 | 15% | Collins `buildClosure` (CdcacCore) |
| **cac-solves-but-budget-clipped** | 9 | 19% | none — CAC decides but 2s budget preempts → Collins → timeout |

**The 9 budget-clipped cases are pure budget tuning** — no algorithmic work
needed, just lift `XOLVER_NRA_CAC_DEADLINE_MS` from 2000 to ~5000. That's the
FIRST concrete Track C lever, supported by direct data.

## Cluster A — `cac-solves-but-budget-clipped` (9 cases)

CAC decides these in 5s but is preempted by the current 2s deadline; Collins
fallback then exhausts the remaining 8s without deciding. Pure budget knob.

Representative families (split sat/unsat in this sample):
- `meti-tarski` (several): polynomial-heavy single asserts, low-var (≤8),
  moderate `nmul` (20–100). CAC's subtropical-then-cell path decides.
- `20180501-Economics-Mulligan` (`MulliganEconomicsModel0004c`): nv=8, na=2,
  neq=4, nmul=4. Low complexity, CAC decides fast given the budget.
- `2019-ezsmt` (`ProveIneq_ISSAC05_Bessack_3_2`): nv=4, na=1, nmul=9. Same.
- `20200911-Pine` (`ball_count_1d_plain.04.seq_lazy_global_4`): nv=56,
  na=1, neq=63, nmul=56. The single big assert is what CAC eats; the 2s
  budget is the only thing keeping it from finishing.

**Lever: TUNE `XOLVER_NRA_CAC_DEADLINE_MS`** — the wins are direct, the
soundness is unchanged (deadline only affects when CAC yields to Collins;
both are sound paths). Verification in progress; expected gain ≈ +9 decisions
on this sample → ~9/48 × 536 ≈ **~100 decisions across the full 536-timeout
corpus** if the cluster ratio holds. Test 5000, 8000, no-deadline (sole-engine).

## Cluster B — `cac-bound` (32 cases, 67%)

CAC engine exceeds 5s of its own search. Structurally diverse:

### B1. Heavy multivariate, single giant assert (Sturm-MBO, Sturm-MGC, hong)
- Profile: nv low or unreadable by my static grep (the SMT2 uses different
  declaration syntax), sz 200KB–550KB, na=1 (one giant polynomial), nmul in
  the **thousands** (`mbo_E10E17` = 35347 `(*`!). Hong: nv 10–12, na=2,
  nmul 19–23, `leafEv` 31–34 (CAC IS running, hits the wall inside the leaf
  isolation loop).
- **Likely wall**: Lazard projection cost — discriminants + pairwise
  resultants on these giant polys produce huge intermediate polynomials.
  The pairwise-resultants superset-vs-cvc5 (audit P2 #36) is sound but
  ~quadratic in the projection set; cvc5's consecutive-only resultants
  would shrink this materially.
- **Lever**: Lazard projection shrinking — match cvc5's consecutive-interval
  resultants instead of the full pairwise set. Soundness needs the per-cell
  origin tracking + the lift argument re-checked under the smaller set.

### B2. Low-var polynomial inequality (meti-tarski residual, kissing, hycomp residual)
- Profile: nv 4–10, na=1, neq 0–5, nmul 10–375. The deep meti-tarski cases
  with high `nmul` (375 on `ProveIneq_ISSAC05_SignPattern_1p_4m_1w_5p_p`)
  burn CAC's subresultant chains.
- **Likely wall**: subresultant chain regeneration in projection (each
  level recomputes resultants from scratch).
- **Lever**: subresultant chain caching across projection recursion.

### B3. Heavy equation count (Geogebra `IsoRightTriangle`, kissing high-dim)
- Profile: nv 5–10, na=1, neq EQUAL TO nv (nv=5 ⇒ neq=5; nv=10 ⇒ neq=5 on
  `kissing_2_5`). Highly equality-constrained — the formula is essentially
  a system of equations with one inequality side-condition.
- **Likely wall**: every equation is a Relation::Eq constraint that CAC
  treats as a delineator, blowing up the boundary set.
- **Lever**: equational-constraint optimization (designate one equation,
  project only w.r.t. it). Mentioned in `CAC.md` §4 as a "completeness/perf
  refinement layered later" — the data says it's needed now for this cluster.

## Cluster C — `collins-bound` (7 cases, 15%)

CAC quickly bails Unknown (insufficient budget OR genuinely unsupported);
Collins's `buildClosure` then burns the wall. These are the cases that
motivated CAC originally — Collins's doubly-exponential closure on
high-degree multivariate.

Representative examples:
- `meti-tarski/Nichols-Plot-Inverted-Pendulum-Fails-1-6-chunk-0086`
- `meti-tarski/asin-8-chunk-0018`
- `2019-ezsmt/ProveIneq_ISSAC05_SignPattern_1p_4m_*`
- `20200911-Pine/ball_count_1d_plain.03.redlog_global_6` (nv=78, neq=100)
- `20180501-Economics-Mulligan/*`

These would benefit from **fixing CAC's quick-bail reason** more than from
tuning Collins. If CAC's `markIncomplete` is over-conservative, the same
cases might actually be CAC-decidable with a more careful fail-closed.

**Lever**: investigate CAC's `lastUnknown()` reasons on these (a sub-tool of
the taxonomy itself — log + categorize the `lastUnknown` strings).

## Cluster D — out-of-CAC families (UltimateAutomizer, Heizmann, LassoRanker, pPDA)

These ~200+ timeouts in the FULL corpus all have:
- High `nvar` (67–1988!) — well beyond CAC's practical reach.
- Very large file sizes (10KB–470KB).
- Many `(declare-fun` (hundreds to thousands).
- Almost no CAC DIAG events even at 5s (`leafEv=0` in the v1 profile).

These cases never get into CAC's cell loop — they're stuck in **preprocessing**:
atomizer / theory presolve / polynomial conversion at the high variable count.
CAC algorithmic levers won't help; the lever is **upstream** (NRA preprocess
or atomization). **Out of scope for Track C in this round.**

## Per-family timeout map (FULL config, 536 cases)

|family | timeout | cluster | suggested lever |
|---|---|---|---|
|UltimateAutomizer | 50 | D | upstream (out of scope) |
|20170501-Heizmann | 50 | D | upstream (out of scope) |
|20200911-Pine | 48 | mix (A/D) | DEADLINE_MS + upstream |
|LassoRanker | 47 | D | upstream (out of scope) |
|2019-ezsmt | 47 | A/C | DEADLINE_MS + collins-bail audit |
|20180501-Economics-Mulligan | 45 | A/C | DEADLINE_MS |
|kissing | 41 | B3 | equational-constraint opt |
|20211101-Geogebra | 40 | B3 | equational-constraint opt |
|zankl | 39 | mix | TBD (small sample) |
|20161105-Sturm-MBO | 24 | B1 | Lazard projection shrinking |
|20220314-Uncu | 21 | A/B | DEADLINE_MS + caching |
|20240407-pPDA | 20 | D | upstream |
|meti-tarski | 19 | A/B2/C | DEADLINE_MS + subresultant cache |
|hycomp | 18 | B2 | subresultant cache |
|hong | 18 | B1/B2 | Lazard shrinking + caching |
|20161105-Sturm-MGC | 9 | B1 | Lazard projection shrinking |

## Track C lever menu (prioritized by data)

1. **`XOLVER_NRA_CAC_DEADLINE_MS` tune** (Cluster A, ~9 in sample, projected
   ~100 in corpus). Direct, fast, low-risk. Verify with single-knob A/B at
   5000/8000/no-deadline. ★ **First Track C round.**
2. **Equational-constraint projection** (Cluster B3, kissing + Geogebra,
   ~60 in corpus). Soundness work — designate the EC, project only via it;
   re-check audit P1/P2 under the smaller set.
3. **Subresultant chain caching** (Cluster B2, hycomp + meti-tarski + hong,
   ~50 in corpus). Cross-level cache keyed by `(f, g, elimVar)`.
4. **Lazard projection shrinking** (Cluster B1, Sturm-MBO + Sturm-MGC + hong,
   ~50 in corpus). Replace pairwise resultants with cvc5's consecutive-only
   set; re-prove the lift argument under the smaller set; this touches the
   audit P2 #36 soundness analysis — needs careful review.
5. **Collins quick-bail audit** (Cluster C, ~30 in corpus). Log
   `lastUnknown()` strings on those timeouts; if `markIncomplete` is
   over-conservative on a common reason, fix that reason.
6. **(Out of scope)** Cluster D upstream work — report to master.

## Verification — finding revised

**First attempt:** `XOLVER_NRA_CAC_DEADLINE_MS=5000` alone — RECOVERED 0/9.
Reason: when Collins is enabled (default HYBRID), Standard-effort `stageCdcac`
runs Collins UNBOUNDED **before** Full-effort `stageCac` ever fires. The 10s
budget is consumed in Standard-effort Collins; extending CAC's Full-effort
deadline doesn't help because Full effort barely runs.

**Second attempt:** `XOLVER_NRA_CAC_ALL_EFFORTS=1` (CAC at Standard effort
too) — RECOVERED **9/9** on the sample. Mechanism: with ALL_EFFORTS, CAC
runs at Standard with its own deadline first, then Collins on Standard, then
both again at Full. On these 9 cases CAC decides at Standard (or first Full)
within its slot, before Collins can grab the budget.

**Same result with `XOLVER_NRA_CAC_ONLY=1`** (CAC-only, no Collins): 9/9.
This matches the v2 NO_COLLINS profile classification — those cases ARE
CAC-decidable in the 10s budget, but the scheduling lets Collins preempt.

### The catch (don't ship ALL_EFFORTS blindly)

The current `stageCac` comment cites a prior A/B: ALL_EFFORTS produced
**50/150 meti-tarski timeouts** (vs the default hybrid), because running the
heavy CAC at every Standard propagation starves the time budget on cases
where Collins would have decided cheaply. Net effect of ALL_EFFORTS on the
full corpus is **NOT** "+~100 decisions"; it's the recovered 9-cluster cases
**minus** the cases Collins would have decided in a tight Standard call.

The next step is a broad differential of `FULL + ALL_EFFORTS=1` vs the
current `FULL` (no ALL_EFFORTS) on the same 714 cases. The delta could be:
- net positive → ship ALL_EFFORTS as a Track C lever (default-OFF flag
  exists, just flip in the FULL bundle).
- net negative → the lever needs per-case selection (run ALL_EFFORTS only
  on cases matching the "CAC-decidable" structural pattern of the 9
  recovered ones: low nv, single-poly heavy-mul, equation-rich).

### Revised lever menu

1. ★ **Broad bench `ALL_EFFORTS=1`** (Track C round 1). The taxonomy says
   the budget-clipped cluster is real (9/48 in this sample); the catch says
   ALL_EFFORTS isn't necessarily a net win. The full-corpus bench decides.
   If net negative, the more careful per-case fallback below.
2. **CAC at Standard with a TIGHT deadline + Collins as fallback** — e.g.
   `ALL_EFFORTS=1 + DEADLINE_MS=500`. CAC gets a 500ms shot at Standard
   first; cases the 9-cluster pattern fits decide; cases that don't get
   passed quickly to Collins. This is the cheap-first hedge.
3. **Bound stageCdcac (Collins) at Standard** with a deadline (new env knob,
   small change to stageCdcac). Lets Collins run at Standard but caps it
   so Full effort always fires. Probably the cleanest lever, but requires
   a new mechanism.

Recommendation: run lever 1 (broad bench), if net negative try lever 2,
otherwise queue lever 3 as a polishing step.

## Track C round 1 — OUTCOME: STOPPED (uncovered a CAC-core soundness bug)

Broad bench of `FULL + XOLVER_NRA_CAC_ALL_EFFORTS=1` on the same 714-case
corpus. Result (`results/track_a/full_alleff*`):

  config              sat unsat unknown timeout UNSOUND
  FULL                57   101    20      536      0
  FULL + ALL_EFFORTS  96   114    28      476    **2**

**+52 decisions, but 2 FALSE-UNSAT** in
`20211101-Geogebra/IsoRightTriangle-Bottema1_12a.smt2` and
`IsoRightTriangle-Bottema1_3a.smt2` (expected SAT, returned UNSAT).

Bug isolation (see task #48): repros with `XOLVER_NRA_CAC=1
XOLVER_NRA_CAC_TRUST_UNSAT=1 XOLVER_NRA_CAC_ALL_EFFORTS=1` AND with
`XOLVER_NRA_CAC=1 XOLVER_NRA_CAC_TRUST_UNSAT=1 XOLVER_NRA_CAC_ONLY=1`
(no EARLY_INFEAS needed). Bug is in **CAC core**, not in any new flag. The
current shipped FULL config (with the 2s `XOLVER_NRA_CAC_DEADLINE_MS`)
TIMES OUT on these cases before the wrong UNSAT emits — that is why
Track A's 714-case FULL run was 0 unsound.

Per master's standing rule ("any QF_NRA/QF_UFNRA 解错 in your lane is
priority-zero"), Track C is STOPPED until #48 lands. ALL_EFFORTS is NOT
shippable as a Track C lever. The lever menu items B1/B2/B3 are also paused
because they all rely on CAC-UNSAT being trustworthy — any unsoundness fix
to the core will rebase the projection paths they touch.

### What the cases look like (for the eventual #48 fix)

5 variables (`m`, `v10`, `v11`, `v8`, `v9`), 9 constraints:
- 4 strict inequalities `m > 0 ∧ v10 > 0 ∧ v11 > 0 ∧ v9 > 0`,
- 4 equalities — `-v8²+1 = 0`, `-v10²+v8²+1 = 0`, `-v11²+v8² = 0`,
  `-v9+1 = 0`,
- 1 big polynomial equation in `m, v10, v11` (the `(a+b+c)³(a+b-c)(b+c-a)
  (c+a-b)` vs `a²b²c²` comparison from the Bottema problem),

with SAT solution: `v8 = ±1, v10 = √2, v11 = 1, v9 = 1, m = ...` (forced
by the bigpoly equation). The pairwise resultant of `-v8²+1` and
`-v10²+v8²+1` w.r.t. `v8` is `(-v10²+2)²`, whose root `√2` is exactly the
algebraic value CAC must sample to find SAT. Hypothesis to test: either
(a) the propagation chain DROPS the `-v10²+2` resultant under some path,
or (b) the algebraic-sample selection at level 1 (`v10`) does not land on
`√2` for the prefixes it tries. cvc5 cdcac decides these cases.
