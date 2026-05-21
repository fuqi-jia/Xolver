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
- `nira/nira_012_unsat_product_lower_bound.smt2` — **CRASH**: `bad optional access` exception. Solver code dereferences an empty `std::optional` somewhere in NIRA path. **High priority** — crashes should never happen.
- `nira/nira_013_sat_polynomial_int_coeff_real_var.smt2` — `2r²-3r+1=0` returns unknown.
- `nira/nira_018_sat_nonlinear_real_to_int.smt2` — `to_int(r²+1) ≥ 1` returns unknown.
- `nira/nira_020_sat_three_vars.smt2` — `r = to_real(i)/to_real(j)` returns unknown.

## known-unsound

- `uflia/uflia_003_unsat_bridge_linear.smt2` — **UNSOUND**: nlcolver returns sat on a clearly UNSAT formula. Both z3 and cvc5 agree unsat. Suspected Nelson-Oppen interface variable propagation between EUF and LIA: the `x=1 ⇒ (f x)≡(f 1)` congruence bridge is not firing. **Highest-priority bug.**
- `lira/lira_012_unsat_is_int_strict_open.smt2` — **UNSOUND**: `is_int r ∧ r > 0 ∧ r < 1` returns sat but is clearly unsat (no integer in (0,1)). Solver appears to ignore the integrality constraint from `is_int` when combined with strict real bounds.
- `nira/nira_009_sat_linear_int_nonlinear_real.smt2` — **UNSOUND**: `i=3 ∧ r>0 ∧ r²=3` should be sat (r=√3≈1.732) but solver returns unsat. NIRA atomizer drops the nonlinear-real branch (related to git commit 0c48497 atomizer regression).
- `nira/nira_010_unsat_bound_mix.smt2` — **UNSOUND**: `i+r>10 ∧ i≤1 ∧ r≤1` should be unsat but solver returns sat. NIRA mixed-type bound propagation broken.
- `nira/nira_019_unsat_floor_below_zero.smt2` — **UNSOUND**: `r≥0 ∧ i=to_int(r) ∧ i<0` should be unsat but solver returns sat. NIRA `to_int` monotonicity not propagating.
