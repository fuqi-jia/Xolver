# NLColver Regression — Known Failures

This file is the **single source of truth** for which regression SMT2 files
are currently expected to fail. The regression runner (`tools/run_regression.py`)
parses this file at startup and treats listed entries leniently:

- **known-fail** → runner reports `KNOWN_FAIL` instead of `UNEXPECTED_FAIL`,
  does *not* fail CTest. Use for cases where the solver returns `unknown`
  but the oracle (z3+cvc5) has an answer.
- **known-unsound** → runner reports `KNOWN_FAIL` but **always** prints a
  loud `!!! UNSOUND` warning. Does *not* fail CTest. Use for confirmed
  unsoundness bugs (solver returned the opposite of oracle).

When a bug is fixed, **delete the corresponding line**. When a new bug is
discovered, add an entry with: relative path, kind, one-line reason.

Format (per line under each section):

    - `<relative-path-under-tests/regression>` — short reason

Lines that don't match this format are ignored — feel free to add prose.

---

## known-fail

- `euf/euf_025_pred_trans.smt2` — Test file uses Int sort under (set-logic QF_UF); LogicFeatureDetector strictly flags the mismatch. Either retype the test as QF_UFLIA or relax the detector.
- `euf/euf_028_sat_bool_fun.smt2` — Bool-codomain function symbols (`P : Bool → Bool`) yield `Theory: unknown (no reason)`. Gap in EUF + Bool-result handling.
- `lira/lira_009_unknown_nonlinear_to_int.smt2` — `(to_int (* x x))` is nonlinear-in-real; LIRA path returns unknown. Expected gap per plan.md §5.
- `nra/nra_001_cubic.smt2` — Univariate cubic with strict `>` and `<` returns unknown. Suspected CDCAC projection / section-lifting gap.
- `uflia/uflia_004_unknown_or_x.smt2` — Disjunction `(or (= x 0) (= x 1))` returns unknown. Mixed UF+LIA combination boundary.
- `lra/lra_010_unsat_eq_chain_break.smt2` — Eq chain `x=y, y=z` + `distinct x z`: solver returns unknown. Transitive disequality not propagated in LRA.
- `lra/lra_021_sat_distinct_3vars.smt2` — n-ary distinct (n≥3) on Reals returns unknown. Likely missing pairwise expansion for distinct on Real sort.
- `lia/lia_015_sat_distinct_3_int.smt2` — n-ary distinct (n≥3) on Ints returns unknown. Same gap as LRA — distinct pairwise expansion missing for arithmetic theories.
- `lia/lia_016_unsat_distinct_too_many.smt2` — n-ary distinct (n≥3) on Ints with tight bounds returns unknown. Same gap.
- `nra/nra_021_unsat_sum_of_squares_plus_one.smt2` — `x²+y²+1 ≤ 0` returns unknown. CDCAC missing sum-of-squares positivity reasoning.
- `nira/nira_004_sat_int_times_real_pos.smt2` — `i*r > 0 ∧ i>0 ∧ r>0` returns unknown. NIRA core gap.
- `nira/nira_006_sat_real_sq_eq_int.smt2` — `r²=4 ∧ to_int(r)=2` returns unknown. NIRA nonlinear + to_int gap.
- `nira/nira_007_unsat_real_sq_neg.smt2` — `r²=-1` returns unknown. NIRA can't refute even classical contradictions.
- `nira/nira_008_sat_to_int_nonlinear_real.smt2` — `r²=4 ∧ to_int(r)≥0` returns unknown.
- `nira/nira_011_sat_bounded_product.smt2` — `(i≥1) ∧ (r≥0) ∧ (i*r ≤ 1)` returns unknown.
- ~~`nira/nira_012_unsat_product_lower_bound.smt2`~~ — **FIXED** in 2026-05-21: hardened `GeneralSimplex::explainLowerConflict` / `explainUpperConflict` against missing bound `reason` optional.
- `nira/nira_013_sat_polynomial_int_coeff_real_var.smt2` — `2r²-3r+1=0` returns unknown.
- `nira/nira_018_sat_nonlinear_real_to_int.smt2` — `to_int(r²+1) ≥ 1` returns unknown.
- `nira/nira_020_sat_three_vars.smt2` — `r = to_real(i)/to_real(j)` returns unknown.
- ~~`nira/nira_023_sat_real_sq_variant.smt2`~~ — **FIXED** in 2026-05-21: univariate quadratic analysis + linear-context integer variable collection.
- `nra/nra_038_sat_ellipse_tangent.smt2` — Ellipse `x²/4+y²=1` tangent to `y=1` at (0,1). CDCAC unknown — projection gap for rational-coefficient ellipses.
- `nra/nra_040_sat_3vars_sphere.smt2` — CDCAC algebraic isolation of `y²+z²+x²-1` with nested algebraic coefficients returns `unknown` (SIGSEGV recovered via signal handler). Still a gap — proper tower reduction for multivariate sphere needed.
- `nra/nra_043_unsat_parabola_below_line.smt2` — `y=x²+1 ∧ y<0` returns unknown. Same family as `nra_021` (sum-of-squares positivity gap).
- `nra/nra_046_unsat_aggregate_positive.smt2` — `(x-1)²+(y-2)²≤-1` returns unknown. Bivariate aggregate positivity gap.
- `nia/nia_032_unsat_modular_chain.smt2` — Chain of `mod` constraints returns unknown. NIA modular reasoning chain depth limited.
- `nira/nira_027_sat_split_nl_lin.smt2` — Mixed `r²≥1 ∧ i≤5 ∧ r≤10` returns unknown. Atomizer routing fails when nonlinear-real and pure-linear-int both present.
- `uflia/uflia_017_unsat_purify_violation.smt2` — `f(x+1)` and `f(2)` under `x=1` should congruence-merge but solver returns unknown. Atomizer purification of `(+ x 1)` inside UF arg missing.
- `lra/lra_044_unsat_distinct_eq_chain.smt2` — `distinct` + eq chain returns unknown. Missing disequality propagation for distinct on Real.
- `lra/lra_045_unsat_neg_eq.smt2` — Negated equality `not(= x y)` with bounds returns unknown. Disequality handling gap in LRA.
- `nia/nia_043_sat_mod_witness.smt2` — `mod` witness existence returns unknown. NIA modular reasoning incomplete.
- `nia/nia_045_sat_mixed_lin_nonlin.smt2` — Mixed linear/nonlinear integer returns unknown. NIA branch lemma generation gap.
- `nra/nra_048_sat_metitarski_polynomial.smt2` — High-degree polynomial sat returns unknown. CDCAC projection gap.
- `nra/nra_050_sat_close_to_root.smt2` — Polynomial with root very close to rational boundary returns unknown. CDCAC interval precision gap.
- `nra/nra_053_sat_polynomial_disjunction.smt2` — Disjunction of polynomial constraints returns unknown. CDCAC covering incomplete for disjunctions.
- `nia/nia_048_sat_verymax_nested_strict.smt2` — VeryMax-style nested strict inequalities `(x>y ∧ y>z ∧ z≥1 ∧ x*z>0)` returns unknown. Likely the AlgebraicIntegerReasoner doesn't handle strict + multiplicative product witness search.
- `nra/nra_054_sat_metitarski_atan_approx.smt2` — meti-tarski atan approximation polynomial returns unknown. CDCAC degree-5 univariate gap with rational endpoints.
- `nra/nra_057_sat_polynomial_band.smt2` — Thin band `y=x² ∧ 1/100 ≤ y ≤ 1/99` returns unknown. CDCAC precision-sensitive rational endpoints.
- `nra/nra_058_sat_metitarski_exp_approx.smt2` — meti-tarski exp(x) approximation `1+x+x²/2 > 0` with `x ∈ [-1/10, 1/10]` returns unknown. Bivariate (x, ex) with rational endpoint gap.
- `nra/nra_062_sat_polynomial_outside_band.smt2` — Disjunction `x<2/5 ∨ x>3/5` returns unknown. Same family as nra_053 (CDCAC disjunction).
- `nra/nra_063_sat_atan_chain_polynomial.smt2` — Multi-var bounded with rational bounds `|x|≤1 ∧ |y|≤1 ∧ |x-y|≤1/10` returns unknown. CDCAC variable ordering or rational endpoints.

## known-unsound

- ~~`uflia/uflia_003_unsat_bridge_linear.smt2`~~ — **FIXED** in 2026-05-21: `backtrackToLevel(0)` now fully resets LIA/LRA solver state, preventing stale bounds from previous model checks.
- ~~`lira/lira_012_unsat_is_int_strict_open.smt2`~~ — **FIXED** in 2026-05-21: `FrontendAdapter` now maps `NT_IS_INT` and `LinearToIntPurifier` lowers `IsInt(r)` to `Eq(r, ToReal(k))` with floor lemmas.
- ~~`lira/lira_020_unsat_is_int_variant_eq.smt2`~~ — **FIXED** (same root cause as lira_012).
- ~~`lira/lira_021_unsat_is_int_variant_negative.smt2`~~ — **FIXED** (same root cause as lira_012).
- ~~`nira/nira_009_sat_linear_int_nonlinear_real.smt2`~~ — **FIXED** in 2026-05-21: univariate quadratic analysis in `checkAssignmentWithSimplex`.
- ~~`nira/nira_010_unsat_bound_mix.smt2`~~ — **FIXED** (same root cause as uflia_003 — stale level-0 state after backtrack).
- ~~`nira/nira_019_unsat_floor_below_zero.smt2`~~ — **FIXED** (same root cause as uflia_003 — stale level-0 state after backtrack).
