# Phase B/C Report — preprocess-deep: QF_LIA convert via SolveEqs ±1-pivot elimination

**Branch:** `agent/preprocess-deep` (base `origin/integration` @ 3a56619)
**Commits:** `86ee85c` (Phase A report), `e1bfa07` (Phase B implementation + tests)
**Decision:** master pivoted the lane from SAT14 (engine-bound, → NIA NLA-cuts) to QF_LIA `convert` (preprocessing-recoverable). See `PHASE-A-REPORT.md`.

---

## TL;DR

`SolveEqs` (the `XOLVER_PP_SOLVE_EQS` var-elimination pass) only eliminated
variables defined by a **bare-variable** equality `x = t` (~80/case on convert).
The QF_LIA `convert` cluster is dominated by **Farkas-style `expr = expr`**
equalities it could not touch. I extended it to **general linear ±1-pivot
elimination**: solve any linear equality `Σ aᵢ·xᵢ = c` for a variable whose
coefficient is ±1 (exact, integer-preserving — no division). On convert this
lifts elimination from ~80 to **~250 variables/case**, collapsing the residual
LIA system to something the linear solver decides quickly.

**Result (convert weakness cases, GAUSS @20 s local), 0 unsound throughout:**
- smallest-30 sample: **22/30 (73 %)** (vs 3/30 = 10 % plain `PP_SOLVE_EQS`)
- full-size-range 55-sample: **16/55 (29 %)** → extrapolated 220-pool ≈ **64 @20 s**
- recovery is **size-dependent**: small/medium cases recover; the large tail is
  bound by **`lia.core` (LIA-solver) scale**, not preprocessing — see §3.1.
- expect the 220-pool recovery to land **higher at the competition timeout**
  (the 20 s local cap is harsh) but the very-large tail needs a faster LIA core.

**Gates:** unit **1033/1033** (+5 gauss tests), regression **668/668** OFF and
ON(GAUSS), **0 unsound**. Pair-soundness matrix **0 unsound** across
{REWRITE, PG_CNF, STRICT_VALIDATION}.

---

## 1. Root-cause of the 9/12 plain-`PP_SOLVE_EQS` timeouts (Phase B diagnosis)

Contrary to the "reconstruct incompleteness / var-ordering / nested-let"
hypothesis, the elimination count was **near-identical** (~80) across solved and
timeout convert cases — the gate fires consistently. The timeouts are **residual
LIA hardness after elimination**: ~80 eliminations leave a ~460-variable system
the simplex/branch solver can't crack in 20 s (z3 solves the original in 0.17 s).

`SolveEqs` only matched `(= barevar t)`. In convert (`convert-jpg2gif-query-1180`,
541 int vars, 268 equalities): **102 are `barevar = expr`, 166 are `expr = expr`**
(e.g. `−z3_11_0_ + z3_31_0_ − 4096·z3_13_12_ − 16384·z3_31_14_ = 0`). **All 166**
have a ±1-coefficient variable that is exactly isolatable; **485 distinct
±1-eligible variables** exist across them — a large untapped elimination pool.

## 2. The extension (commit `e1bfa07`)

`SolveEqs::tryGeneralEliminate` (gated `setGeneralLinear`, env
`XOLVER_PP_SOLVE_EQS_GAUSS`):
1. Parse the equality with `extractLinearConstraint` → `Σ coeffs[v]·v = rhs`
   (returns false for anything nonlinear → bilinear Farkas products skipped).
2. Pick the first (deterministic, name-sorted) pivot `xⱼ` with `|coeffⱼ| = 1`,
   not UF/array-shared (`unsafeVars_`), of Int/Real sort with same-sort cohort.
3. Build the exact replacement `xⱼ = ∓(Σᵢ≠ⱼ coeffs[i]·xᵢ − rhs)` and substitute.

**Soundness guarantees:**
- `|coeffⱼ| = 1` → reconstruction is exact integer (no division → no dropped
  integer solutions). `fits_slong` + `den == 1` const guard.
- Coefficients are taken from the *original* equation and **grafted as a tree**
  by `substitute()` (variable node → replacement subtree), so coefficients
  **never multiply/grow** across chained eliminations.
- Reuses the existing `unsafeVars_` Nelson-Oppen guard (UF/array-shared pivots
  pinned) — same protection as the bare-var path.
- Replacement is linear + reconstructable by construction → `ModelConverter`
  replays it exactly; every returned `sat` is model-validated (invariant 1).

**Logic restriction:** GAUSS runs only on **linear** arith logics. On NIA/NRA/NIRA,
substituting a linear definition into nonlinear terms changes the polynomial
structure the theory reasoner relies on — sound, but it floored `nia_089`
(sat → unknown). The gate excludes nonlinear logics; the convert target is pure
linear, so this costs nothing.

## 3. Measurement

| config | convert recovery (local @20 s) | unsound |
|---|---|---|
| default | 0 | 0 |
| `PP_SOLVE_EQS` (bare-var only) | 3/30 (10 %) | 0 |
| `PP_SOLVE_EQS_GAUSS`, smallest-30 | **22/30 (73 %)** | 0 |
| `PP_SOLVE_EQS_GAUSS`, full-size-range 55 | **16/55 (29 %)** → ≈64/220 | 0 |

Elimination count jumps ~80 → ~250/case (and 710/1719 on the largest case).
Local 20 s underestimates the competition timeout; expect higher on the server.

### 3.1 The recovery ceiling is the LIA solver, not preprocessing

On the largest convert case (`convert-jpg2gif-query-1619`, 1719 int vars,
227 KB) GAUSS eliminates **710 variables** — yet it still times out.
`ARITH_STAGE_PROF` shows why: `lia.core` is invoked **hundreds of times** in the
CDCL(T) loop (pipeline-calls 57→110→161→205…, ~10 ms each) on the still-large
(~1000-var) residual. A 151 KB case that **z3 solves in 4.75 s** still times out
in xolver at **90 s**. So the binding constraint past preprocessing is the
**LIA theory solver's scale** (simplex/branch per-call cost × call count), not
the formula size GAUSS already cut. **This is the `lia-lra-deep` lane** — GAUSS
maximizes the preprocessing lever (it removes ~40–60 % of variables); closing
the large-file tail needs a faster/incremental `lia.core`. Cross-lane handoff
recommended.

## 4. Soundness gates

- Unit: **1033/1033** (added 5 `SolveEqs[gauss]` tests: ±1 pivot, scaled-var
  refusal, no-±1 refusal, UF-shared skip, flag-off no-op).
- Regression: **668/668** default and GAUSS-ON, **0 unsound, 0 completeness loss**.
- Pair-soundness matrix (full reg, GAUSS combined with each / all of REWRITE,
  PG_CNF, STRICT_VALIDATION): **0 unsound**. All 40 failures under all-PP-on are
  `sat → unknown` (sound floors). 38 are pre-existing (STRICT/REWRITE/PG_CNF,
  not GAUSS — confirmed by minus-GAUSS run = 38).

## 5. Known interaction routed to A5: GAUSS × STRICT_VALIDATION (2 cases)

`lia_047`, `lira_026`: `sat` under GAUSS-only and under STRICT-only, but
`unknown` under **both**. Root cause: the STRICT model-validation gate
(`Solver.cpp:~1643`) runs **before** `ModelConverter.reconstruct()`
(`Solver.cpp:~1790`), so the GAUSS-eliminated variables are absent from the
model when STRICT validates against the original assertions →
Indeterminate → floored. **GAUSS's model is correct** (GAUSS-only returns a
validated `sat`); this is a STRICT_VALIDATION↔ModelConverter ordering gap
(affects bare-var `SolveEqs` too in principle; GAUSS surfaces it via the larger
elimination set). Sound (only sat→unknown), both flags default-OFF. **Routed to
A5** (owner of STRICT_VALIDATION + ModelConverter ordering); the fix is to
reconstruct eliminated vars into the model before strict validation. Not fixed
here to avoid destabilizing A5's verdict-finalization path (38 other STRICT
interactions).

## 6. rings_preprocessed (142) — explicitly deprioritized
All **142 are UNSAT**. Var-elimination is a SAT/equality-chain lever, not an
UNSAT-proving one; `PP_SOLVE_EQS(+GAUSS)` recovers 0/4. These need
modular/cutting-plane reasoning — out of the preprocessing lane. Catalog should
drop `rings_preprocessed` from preprocess-deep targets.

## 7. Promotion path
`XOLVER_PP_SOLVE_EQS_GAUSS` is default-OFF, layered on `XOLVER_PP_SOLVE_EQS`
(also default-OFF). For default-ON: (a) promote `PP_SOLVE_EQS` first (its own
A5-tracked reconstruct floor), (b) land the A5 STRICT×ModelConverter ordering
fix so the GAUSS×STRICT pair is clean, (c) server differential to confirm the
220-pool recovery and the 1958 oracle-blind wins are untouched (GAUSS is
linear-logic-only, so QF_NIA/NRA wins are structurally unaffected).
