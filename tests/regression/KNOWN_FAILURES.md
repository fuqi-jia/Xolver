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
- `nra/nra_065_unsat_two_circles_one_line.smt2` — CDCAC `sector(-inf, -0.8)` SIGSEGV (HIGH); also unknown-via-handler. See known-unsound section for crash details.
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
- `nra/nra_064_unsat_three_circles_no_common.smt2` — Three unit circles (centered at 0, e1, e2) have no common intersection — returns unknown. CDCAC multivariate disjoint-cell coverage gap.
- `nra/nra_069_unsat_parabola_below_zero.smt2` — `y=x²+1 ∧ y<0` returns unknown. Direct SOS positivity gap (companion to nra_021/043/046).
- `nra/nra_073_unsat_3vars_no_real.smt2` — `x²+y²+z²=-1` returns unknown. 3-var SOS positivity gap; CDCAC does not refute negative-RHS sum-of-squares equality.
- `nra/nra_082_sat_null_projection_avoid.smt2` — `y*(x-1)=0 ∧ y>0` (forces x=1) returns unknown. NullificationAnalyzer not used or factor-case-split missing.
- `nra/nra_087_sat_icp_narrow_box.smt2` — Narrow box around (1,1) with `xy ∈ [0.99, 1.01]` returns unknown. ICP precision near point-feasible region.
- `nia/nia_058_unsat_diophantine_multi_eq.smt2` — Two linear diophantine eqs with explicit unique negative solution + bound `x≥0` returns unknown. Linear elimination over integers not propagating to bound.
- `nia/nia_061_sat_crt_3_moduli.smt2` — 3-modulus CRT (`x≡2(mod 3) ∧ x≡3(mod 5) ∧ x≡2(mod 7)`) returns unknown. NIA mod-chain depth gap (companion to nia_032).
- `nia/nia_062_unsat_crt_inconsistent.smt2` — Inconsistent CRT (`x≡1(mod 6) ∧ x≡0(mod 3)`) returns unknown. NIA modular consistency check missing.
- `nia/nia_064_unsat_polynomial_inequality_clash.smt2` — `x²<y ∧ y≤x ∧ x≥2` should chain to `x²<x` contradiction with `x≥2` — returns unknown. Polynomial-vs-linear chain reasoning gap.

### SEGV minimization study (nra_065 family) — only nra_065 still crashes
- `nra/nra_093_segv_repro_min_two_circles.smt2` — Two intersecting unit circles (NO line) — `unknown` not SEGV. **Negative result: removing `y=x` from nra_065 eliminates the crash. SEGV root cause requires line-equality interaction.**
- nra_094–100 (other minimization variants) all return `sat` correctly.

### SOS positivity systematic gap (CDCAC priority)
- `nra/nra_104_unsat_sos_2var_minus_neg.smt2` — `x²+y² ≤ -1/1000` returns unknown.
- `nra/nra_106_unsat_sos_offset_const.smt2` — `(x-1)²+(y-2)²+1 ≤ 0` returns unknown.
- `nra/nra_108_unsat_sos_difference_squared.smt2` — `(x-y)² < 0` returns unknown.
- `nra/nra_109_unsat_sos_3var_strict.smt2` — `x²+y²+z² < 0` returns unknown.
- `nra/nra_110_unsat_sos_4var_strict.smt2` — 4-var SOS < 0 returns unknown.
- `nra/nra_112_unsat_sos_product_squares.smt2` — `x²·y² < 0` returns unknown.
- `nra/nra_113_unsat_sos_eq_neg.smt2` — `x²+y² = -2` returns unknown.

### NIA modular chain gaps
- `nia/nia_068_unsat_crt_2mod_inconsistent.smt2` — `mod x 4 = 0 ∧ mod x 2 = 1` returns unknown. Non-coprime modulus consistency missing.
- `nia/nia_069_sat_crt_4mod.smt2` — 4-modulus CRT returns unknown.
- `nia/nia_070_sat_crt_5mod.smt2` — 5-modulus CRT returns unknown.
- `nia/nia_071_unsat_crt_non_coprime.smt2` — `mod x 6 = 1 ∧ mod x 4 = 2` returns unknown.
- `nia/nia_074_sat_mod_with_ineq.smt2` — `mod x 7 = 3 ∧ 20≤x≤30` returns unknown.
- `nia/nia_075_unsat_mod_with_ineq_empty.smt2` — `mod x 10 = 7 ∧ 0≤x≤6` returns unknown.
- `nia/nia_079_sat_mod_via_eq.smt2` — `x=7 ∧ mod x 3 = 1` returns unknown. (Should be trivial.)

## known-unsound

- ~~`uflia/uflia_003_unsat_bridge_linear.smt2`~~ — **FIXED** in 2026-05-21: `backtrackToLevel(0)` now fully resets LIA/LRA solver state, preventing stale bounds from previous model checks.
- ~~`lira/lira_012_unsat_is_int_strict_open.smt2`~~ — **FIXED** in 2026-05-21: `FrontendAdapter` now maps `NT_IS_INT` and `LinearToIntPurifier` lowers `IsInt(r)` to `Eq(r, ToReal(k))` with floor lemmas.
- ~~`lira/lira_020_unsat_is_int_variant_eq.smt2`~~ — **FIXED** (same root cause as lira_012).
- ~~`lira/lira_021_unsat_is_int_variant_negative.smt2`~~ — **FIXED** (same root cause as lira_012).
- ~~`nira/nira_009_sat_linear_int_nonlinear_real.smt2`~~ — **FIXED** in 2026-05-21: univariate quadratic analysis in `checkAssignmentWithSimplex`.
- ~~`nira/nira_010_unsat_bound_mix.smt2`~~ — **FIXED** (same root cause as uflia_003 — stale level-0 state after backtrack).
- ~~`nira/nira_019_unsat_floor_below_zero.smt2`~~ — **FIXED** (same root cause as uflia_003 — stale level-0 state after backtrack).
- `nra/nra_065_unsat_two_circles_one_line.smt2` — **SIGSEGV** (HIGH PRIORITY) during CDCAC `sector(-inf, -0.75)` lifting on `x²+y²=1 ∧ (x-1)²+y²=1 ∧ y=x`. Delta-debugging (nra_093–100) shows the crash requires the linear equality `y=x` together with both circles; removing any one (nra_093 = two circles only) eliminates the crash (becomes unknown).
- ~~`nia/nia_077_sat_mod_2var.smt2`~~ — **FIXED** in 2026-05-21: three changes — (1) try `localSearch` before emitting pending linear lemmas so it actually runs, (2) sync `hasLower/hasUpper` in `DomainStore::restrictToFiniteSet` so local-search candidates respect fixed values like `x=7`, (3) accept `vNext <= curViol` in hill-climbing to cross variable-coupling ridges (e.g. `r3=r1`).

### J-batch findings (SMT-COMP grade, complex multi-constraint systems)
- `nra/nra_120_unsat_5conic_intersection.smt2` — 5 conic curves with disjoint feasibility — unknown.
- `nra/nra_121_sat_kinematics_orbit.smt2` — orbital kinematics 3-poly system — unknown.
- `nra/nra_122_unsat_3_quadrics_disjoint.smt2` — 3 disjoint spheres — unknown.
- `nra/nra_124_sat_robotic_workspace.smt2` — 2-link robot arm reachability — unknown.
- `nra/nra_126_sat_polynomial_lyapunov.smt2` — Lyapunov decrease in annulus — unknown.
- `nra/nra_128_sat_geometric_packing.smt2` — 2-disk packing — unknown.
- `nra/nra_131_sat_brown_2001_relaxed.smt2` — Brown'01 dim-3 relaxed — unknown.
- `nra/nra_134_unsat_metitarski_negation.smt2` — meti-tarski exp negation — unknown.
- `nra/nra_135_unsat_amzi_classic.smt2` — Cauchy-Schwarz refutation — unknown.
- `nra/nra_136_sat_amzi_tight.smt2` — CS equality at (1,1,1) — unknown.
- `nra/nra_137_unsat_strict_cs_violation.smt2` — strict CS violation — unknown.
- `nra/nra_138_sat_huge_coeff.smt2` — huge rational coefficient — unknown.
- `nia/nia_090_unsat_partition_sum_no_solution.smt2` — 3-square-distinct partition — unknown.
- `nia/nia_095_unsat_collatz_step_wrong.smt2` — Collatz step ITE-based — unknown.
- `nia/nia_097_unsat_squares_chain.smt2` — squares chain inequality — unknown.
- `nia/nia_098_sat_huge_modulus.smt2` — huge modulus (10^15) — unknown.
- `uflra/uflra_008_sat_array_with_real.smt2` — array-as-fun 5-element sum of fractions — unknown.

### K-batch: SOTA-grade depth findings (2026-05-22)
- `lia/lia_050_sat_sudoku_row.smt2` — Sudoku row (9 distinct 1-9) returns unknown. LIA n-ary distinct (n=9) gap (extension of lia_015 family).
- `ufnra/ufnra_006_sat_circle_fn.smt2` — `f(x)²+x²=1 ∧ x=0` returns unknown. UFNRA nonlinear-real + UF combination.
- `ufnra/ufnra_007_unsat_circle_fn_conflict.smt2` — Same circle with `x=2` should be unsat (x²+f(x)²≥4>1) returns unknown.

### K-batch unsound (high priority)
- `nra/nra_127_sat_swap_compatible.smt2` — **UNSOUND**: `a+b=c+d ∧ ab=cd ∧ distinct(a+c, b+d) ∧ all>0` is SAT (witness (1,2,1,2)) but solver returns unsat. Twin oracle (z3+cvc5) agrees sat. NRA polynomial-system soundness bug.
