# Zolver Regression — Known Failures

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

- ~~`lira/lira_009_sat_nonlinear_to_int.smt2`~~ — **FIXED** in 2026-05-25 by Cap. 8c `ToIntDefinitionalLowerer` + logic upgrade `QF_LIRA → QF_NIRA`. The lowerer lifts `(to_int (* x x))` to a fresh `i_t` plus the bridge `r_t = (* x x)` and floor sandwich `(<= (to_real i_t) r_t)`, `(< r_t (+ (to_real i_t) 1))`; the upgrade routes the nonlinear bridge to NRA-CDCAC.
- ~~`nra/nra_001_sat_cubic.smt2`~~ — **FIXED** in 2026-05-25: `PolynomialConverter::collectRec` now accepts `Kind::ConstReal` integer-valued exponents in `Kind::Pow` (SOMTParser emits `(^ x 3)`'s exponent as ConstReal with denominator 1, so the previous ConstInt-only check silently failed every nontrivial power atom).
- ~~`lra/lra_010_unsat_eq_chain_break.smt2`~~ — **FIXED** in 2026-05-25 (verified passing; root cause: NaryDistinctLowerer + LRA disequality propagation (b8bc81f)).
- ~~`lra/lra_021_sat_distinct_3vars.smt2`~~ — **FIXED** in 2026-05-25 (verified passing; root cause: NaryDistinctLowerer expansion (b8bc81f)).
- ~~`lia/lia_015_sat_distinct_3_int.smt2`~~ — **FIXED** in 2026-05-25 (verified passing; root cause: NaryDistinctLowerer expansion (b8bc81f)).
- ~~`lia/lia_016_unsat_distinct_too_many.smt2`~~ — **FIXED** in 2026-05-25 (verified passing; root cause: NaryDistinctLowerer expansion (b8bc81f)).
- ~~`nra/nra_021_unsat_sum_of_squares_plus_one.smt2`~~ — **FIXED** in 2026-05-23 (pseudoRemainder + level-0 projection bundle).
- ~~`nira/nira_004_sat_int_times_real_pos.smt2`~~ — **FIXED** in 2026-05-24: NiraSolver bounded-complete enumeration now pins half-bounded integer variables to their single available bound (single-point heuristic), so `i > 0 ∧ r > 0 ∧ i*r > 0` finds the witness at `i = 1`. Non-exhaustive — return Unknown rather than UNSAT if pin fails.
- ~~`nira/nira_006_sat_real_sq_eq_int.smt2`~~ — **FIXED** in 2026-05-24 (pure-real subproblem delegated to CDCAC after substituting `i = to_int(r)` does not bind, plus heuristic pin).
- ~~`nira/nira_007_unsat_real_sq_neg.smt2`~~ — **FIXED** in 2026-05-24: new `NiraSolver::checkPureSubproblems` routes the residual real-only polynomial system through a fresh `CdcacSolver`, picking up CDCAC's SOS-positivity refutation for `r² + 1 = 0`.
- ~~`nira/nira_008_sat_to_int_nonlinear_real.smt2`~~ — **FIXED** in 2026-05-24 (pure-subproblem delegation handles `r²=4` directly; `to_int(r) ≥ 0` flows through the linear stage).
- ~~`nira/nira_011_sat_bounded_product.smt2`~~ — **FIXED** in 2026-05-24 (single-point pin heuristic — `i = 1` paired with the simplex check is a witness for `i*r ≤ 1`).
- ~~`nira/nira_012_unsat_product_lower_bound.smt2`~~ — **FIXED** in 2026-05-21: hardened `GeneralSimplex::explainLowerConflict` / `explainUpperConflict` against missing bound `reason` optional.
- ~~`nira/nira_013_sat_polynomial_int_coeff_real_var.smt2`~~ — **FIXED** in 2026-05-24 (pure-subproblem delegation routes the univariate quadratic `2r²-3r+1=0` to CDCAC, which finds roots r ∈ {1/2, 1}).
- ~~`nira/nira_018_sat_nonlinear_real_to_int.smt2`~~ — **FIXED** in 2026-05-25 by Cap. 8c `ToIntDefinitionalLowerer`. The lowerer accepts nonlinear `to_int` arguments unconditionally (the previous `LinearToIntPurifier` rejected them) and routes `r_t = (+ (* r r) 1)` to NIRA.
- ~~`nira/nira_020_sat_three_vars.smt2`~~ — **FIXED** in 2026-05-25 by Cap. 8a `UnconditionalConstantPropagation` (collect `i=2, j=3` from top-level unconditional conjuncts and substitute globally — but never under UF applications, to preserve EUF congruence) + Cap. 8b `ToRealLiteralFold` (`(to_real 2) → 2`, `(/ 2 3) → 2/3`).
- ~~`nira/nira_023_sat_real_sq_variant.smt2`~~ — **FIXED** in 2026-05-21: univariate quadratic analysis + linear-context integer variable collection.
- ~~`nra/nra_038_sat_ellipse_tangent.smt2`~~ — **FIXED** in 2026-05-23: pseudoRemainder bug fix + level-0 projection trigger (`RationalPolynomial::pseudoRemainder` was using post-multiplication leading coefficient instead of pre-multiplication, causing SubresultantEngine to never reduce degree when divisor's leading coefficient was non-constant; this broke all CDCAC projection for non-trivial cases).
- ~~`nra/nra_040_sat_3vars_sphere.smt2`~~ — **FIXED** in 2026-05-25 by Cap. 10 `CandidateModelSearch` (validator-gated). Strategy 10a's low-height rational enumeration finds the witness `(x=1, y=0, z=0)` and the arithmetic evaluator confirms it satisfies the sphere and `x ≥ 9/10`. Closed by validator-gated SAT witness search, not by complete NRA reasoning.
- ~~`nra/nra_065_unsat_two_circles_one_line.smt2`~~ — **FIXED** in 2026-05-22: 4 coordinated fixes in LibpolyBackend (`rootBelongsTo` replaced with sign+gcd two-tier check), LibPolyKernel (`pseudoRemainderWithScale` and `degree` corrected for non-main variables), and CdcacCore (`mergeRoots` now refines rational-algebraic adjacency to avoid zero-width sectors). Solver now correctly returns `unsat`.
- ~~`nra/nra_043_unsat_parabola_below_line.smt2`~~ — **FIXED** in 2026-05-23 (pseudoRemainder + level-0 projection bundle).
- ~~`nra/nra_046_unsat_aggregate_positive.smt2`~~ — **FIXED** in 2026-05-23 (pseudoRemainder + level-0 projection bundle).
- ~~`nia/nia_032_sat_modular_chain.smt2`~~ — **FIXED** in 2026-05-24: new `ModularConsistencyChecker` preprocessing pass detects `(= (mod x N) c)` patterns + integer bounds, runs CRT to combine residues and either emit `false` (CRT-inconsistent or finite-range-empty) or pin `x = candidate` (single witness in range). Runs before `IntDivModLowerer` so the mod structure is still inspectable. Same pass also resolves nia_061/062/068/069/071/074/075/098.
- ~~`nira/nira_027_sat_split_nl_lin.smt2`~~ — **FIXED** in 2026-05-24 (pure-subproblem delegation: `r² ≥ 1` is purely real after `i ≤ 5` is excluded from the polynomial set; CDCAC returns sat, NIRA forwards).
- ~~`uflia/uflia_017_unsat_purify_violation.smt2`~~ — **FIXED** in 2026-05-25 (verified passing; root cause: BoolSubtermPurifier + UfInArithPurifier (1cedd97)).
- ~~`lra/lra_044_unsat_distinct_eq_chain.smt2`~~ — **FIXED** in 2026-05-25 (verified passing; root cause: NaryDistinctLowerer expansion (b8bc81f)).
- ~~`lra/lra_045_unsat_neg_eq.smt2`~~ — **FIXED** in 2026-05-25 (verified passing; root cause: LRA disequality propagation (b8bc81f)).
- ~~`nia/nia_043_sat_mod_witness.smt2`~~ — **FIXED** in 2026-05-25 by Cap. 9 `CompleteFiniteDomainEnumerator` (validator-gated). The frontend lowers `(mod x 5)=2` to `x=5q+2`; Cap. 1 eliminates `x↦5q+2`, Cap. 2 defines `y↦(5q+2)²`, Cap. 4 bounds `q∈[0,3]`, Cap. 9 enumerates and `IntegerModelValidator` confirms a witness (e.g. q=0,x=2,y=4). SAT. (Plan routed this through Cap. 6, but with the existing mod-lowering it closes via the finite-domain enumerator.)
- ~~`nia/nia_045_sat_mixed_lin_nonlin.smt2`~~ — **FIXED** in 2026-05-25 by the theory-check presolve (Cap. 2 `PolynomialDefSubstitution` + Cap. 4 + Cap. 9, validator-gated): Cap. 1 eliminates `x↦5−y`, Cap. 2 defines `z↦5y−y²`, Cap. 4 turns `z≥0` into `y∈[0,5]`, Cap. 9 enumerates `y∈{0..5}` and `IntegerModelValidator` confirms a model (e.g. y=0,x=5,z=0). Also independently reachable via Cap. 10 `CandidateModelSearch` as a fallback. SAT (validator-gated).
- ~~`nra/nra_048_sat_metitarski_polynomial.smt2`~~ — **FIXED** in 2026-05-23 (same pseudoRemainder + level-0 projection fix as nra_038).
- ~~`nra/nra_050_sat_close_to_root.smt2`~~ — **FIXED** in 2026-05-25: two coordinated fixes — (1) `LibpolyBackend::refineRootInterval` now refines the bracketing interval _within_ a single call instead of just one libpoly step (it was re-isolating from scratch each entry, so caller-driven loops never made progress past the initial bracket); (2) `LibpolyBackend::validateRootIsolation` retries refinement when adjacent algebraic intervals touch (libpoly emits `[3/4..1]` and `[1..5/4]` for the roots 99/100 and 101/100, which are correct but abutting). Solves the "root near rational boundary" precision case.
- ~~`nra/nra_053_sat_polynomial_disjunction.smt2`~~ — **FIXED** in 2026-05-25 (rolled in via the validateRootIsolation/refineRootInterval pair: disjunction tests routed through CDCAC now survive the touching-interval guard).
- ~~`nia/nia_048_sat_verymax_nested_strict.smt2`~~ — **FIXED** in 2026-05-25 by Cap. 10 `CandidateModelSearch` (validator-gated). Strategy 10a's low-height integer enumeration finds the witness `(x=3, y=2, z=1)` and the arithmetic evaluator confirms it satisfies every original assertion. Closed by validator-gated SAT witness search, not by complete NIA reasoning.
- ~~`nra/nra_057_sat_polynomial_band.smt2`~~ — **FIXED** in 2026-05-25 (same refineRootInterval + validateRootIsolation pair as nra_050).
- ~~`nra/nra_058_sat_metitarski_exp_approx.smt2`~~ — **FIXED** in 2026-05-23 (same pseudoRemainder + level-0 projection fix).
- ~~`nra/nra_062_sat_polynomial_outside_band.smt2`~~ — **FIXED** in 2026-05-23 (same fix).
- ~~`nra/nra_063_sat_atan_chain_polynomial.smt2`~~ — **FIXED** in 2026-05-23 (same fix).
- ~~`nra/nra_064_unsat_three_circles_no_common.smt2`~~ — **FIXED** in 2026-05-23 (same fix).
- ~~`nra/nra_069_unsat_parabola_below_zero.smt2`~~ — **FIXED** in 2026-05-23 (pseudoRemainder + level-0 projection bundle).
- ~~`nra/nra_073_unsat_3vars_no_real.smt2`~~ — **FIXED** in 2026-05-23 (pseudoRemainder + level-0 projection bundle).
- ~~`nra/nra_082_sat_null_projection_avoid.smt2`~~ — **FIXED** in 2026-05-23 (pseudoRemainder + level-0 projection bundle).
- ~~`nra/nra_087_sat_icp_narrow_box.smt2`~~ — **FIXED** in 2026-05-23 (same pseudoRemainder + level-0 projection fix).
- ~~`nia/nia_058_unsat_diophantine_multi_eq.smt2`~~ — **FIXED** in 2026-05-25 by Cap. 5 `IntLinearEqualityCoreHNF` (Smith Normal Form). System `[[2,3],[5,7]]·(x,y)=(5,11)` has SNF `D=diag(1,1)`; particular integer solution `x=-2, y=3`, both parameter-free ⇒ `DerivedFixedValue`. Substituting `x=-2` into `x≥0` ⇒ `-2≥0` ⇒ `DerivedConflict {2x+3y=5, 5x+7y=11, x≥0}`. UNSAT.
- ~~`nia/nia_061_sat_crt_3_moduli.smt2`~~ — **FIXED** in 2026-05-24 (ModularConsistencyChecker preprocessing pass).
- ~~`nia/nia_062_unsat_crt_inconsistent.smt2`~~ — **FIXED** in 2026-05-24 (ModularConsistencyChecker preprocessing pass).
- ~~`nia/nia_064_unsat_polynomial_inequality_clash.smt2`~~ — **FIXED** in 2026-05-25 by Cap. 7 `BoundChainComposer` + Cap. 4 `UnivariatePolySignAnalyzer`. `x²<y` (lower-bounds y) and `y≤x` (upper-bounds y) compose to `x²<x` (`x²−x<0`); root isolation gives roots {0,1}, negative on the open interval (0,1), which contains no integer ⇒ `DerivedConflict {x²<y, y≤x}`. UNSAT.

### SEGV minimization study (nra_065 family) — RESOLVED (2026-05-22)
- ~~`nra/nra_093_segv_repro_min_two_circles.smt2`~~ — delta-debug control case; was `unknown`, now resolved by the same nra_065 fix bundle (root coprimality + rational-algebraic merge).
- nra_094–100 (other minimization variants) all return `sat` correctly.

### SOS positivity systematic gap (CDCAC priority)
- ~~`nra/nra_104_unsat_sos_2var_minus_neg.smt2`~~ — **FIXED** in 2026-05-23 (pseudoRemainder + level-0 projection bundle).
- ~~`nra/nra_106_unsat_sos_offset_const.smt2`~~ — **FIXED** in 2026-05-23 (pseudoRemainder + level-0 projection bundle).
- ~~`nra/nra_108_unsat_sos_difference_squared.smt2`~~ — **FIXED** in 2026-05-24: required two further low-level fixes — (1) `RationalPolynomial::addTerm` now canonicalizes the monomial key (sort by VarId, drop var^0 factors), without which GcdEngine's `pCheck.terms() != pNorm.terms()` verification was spuriously failing on multivariate quotients; (2) `tryExactDivide` was generalized into a recursive multivariate exact-division routine that handles non-constant lc(divisor) by delegating leading-coefficient divisions to `polyExactDivide`, which recurses on the structure of the divisor.
- ~~`nra/nra_109_unsat_sos_3var_strict.smt2`~~ — **FIXED** in 2026-05-23 (pseudoRemainder + level-0 projection bundle).
- ~~`nra/nra_110_unsat_sos_4var_strict.smt2`~~ — **FIXED** in 2026-05-23 (pseudoRemainder + level-0 projection bundle).
- ~~`nra/nra_112_unsat_sos_product_squares.smt2`~~ — **FIXED** in 2026-05-24 (same multivariate exact-division generalization as nra_108; the divisor's leading coefficient `2x²` was non-constant, so the previous algorithm bailed out).
- ~~`nra/nra_113_unsat_sos_eq_neg.smt2`~~ — **FIXED** in 2026-05-23 (pseudoRemainder + level-0 projection bundle).

### NIA modular chain gaps
- ~~`nia/nia_068_unsat_crt_2mod_inconsistent.smt2`~~ — **FIXED** in 2026-05-24 (ModularConsistencyChecker preprocessing pass).
- ~~`nia/nia_069_sat_crt_4mod.smt2`~~ — **FIXED** in 2026-05-24 (ModularConsistencyChecker preprocessing pass).
- ~~`nia/nia_070_sat_crt_5mod.smt2`~~ — **FIXED** in 2026-05-24 (ModularConsistencyChecker preprocessing pass).
- ~~`nia/nia_071_unsat_crt_non_coprime.smt2`~~ — **FIXED** in 2026-05-24 (ModularConsistencyChecker preprocessing pass).
- ~~`nia/nia_074_sat_mod_with_ineq.smt2`~~ — **FIXED** in 2026-05-24 (ModularConsistencyChecker preprocessing pass).
- ~~`nia/nia_075_unsat_mod_with_ineq_empty.smt2`~~ — **FIXED** in 2026-05-24 (ModularConsistencyChecker preprocessing pass).
- ~~`nia/nia_079_sat_mod_via_eq.smt2`~~ — **FIXED** in 2026-05-24 (ModularConsistencyChecker preprocessing pass — bound `x = 7` plus `mod x 3 = 1` pins via the single-candidate branch).

## known-unsound

- ~~`nra/nra_054_sat_metitarski_atan_approx.smt2`~~ — **FIXED** in 2026-05-23: root cause was `RationalPolynomial::pseudoRemainder` reading post-multiplication leading coefficient instead of pre-multiplication, so SubresultantEngine never reduced degree when divisor's lc was non-constant in the elimination variable. CDCAC projection silently produced wrong polynomials, leading to incomplete level-0 root sets and over-generalised sector cells. Fixed by capturing `lcRem` before scaling rem by `lcQ` in `RationalPolynomial::pseudoRemainder`, plus adding a level-0 `needsProjection` trigger in `CdcacCore::solveLevel`. Solver now returns sat. This fix also resolved nra_038/048/058/062/063/064/087/124/127/128.
- ~~`uflia/uflia_003_unsat_bridge_linear.smt2`~~ — **FIXED** in 2026-05-21: `backtrackToLevel(0)` now fully resets LIA/LRA solver state, preventing stale bounds from previous model checks.
- ~~`lira/lira_012_unsat_is_int_strict_open.smt2`~~ — **FIXED** in 2026-05-21: `FrontendAdapter` now maps `NT_IS_INT` and `LinearToIntPurifier` lowers `IsInt(r)` to `Eq(r, ToReal(k))` with floor lemmas.
- ~~`lira/lira_020_unsat_is_int_variant_eq.smt2`~~ — **FIXED** (same root cause as lira_012).
- ~~`lira/lira_021_unsat_is_int_variant_negative.smt2`~~ — **FIXED** (same root cause as lira_012).
- ~~`nira/nira_009_sat_linear_int_nonlinear_real.smt2`~~ — **FIXED** in 2026-05-21: univariate quadratic analysis in `checkAssignmentWithSimplex`.
- ~~`nira/nira_010_unsat_bound_mix.smt2`~~ — **FIXED** (same root cause as uflia_003 — stale level-0 state after backtrack).
- ~~`nira/nira_019_unsat_floor_below_zero.smt2`~~ — **FIXED** (same root cause as uflia_003 — stale level-0 state after backtrack).
- ~~`nra/nra_065_unsat_two_circles_one_line.smt2`~~ — **FIXED** in 2026-05-22 (see known-fail section for fix details). Combined `rootBelongsTo` unsoundness + libpoly `prem`/`degree` non-main-var bugs + `mergeRoots` zero-width sector. Delta-debug (nra_093 = two circles, no line) was the control case that confirmed `y=x` interaction; both now pass after fix.
- ~~`nia/nia_077_sat_mod_2var.smt2`~~ — **FIXED** in 2026-05-21: three changes — (1) try `localSearch` before emitting pending linear lemmas so it actually runs, (2) sync `hasLower/hasUpper` in `DomainStore::restrictToFiniteSet` so local-search candidates respect fixed values like `x=7`, (3) accept `vNext <= curViol` in hill-climbing to cross variable-coupling ridges (e.g. `r3=r1`).

### J-batch findings (SMT-COMP grade, complex multi-constraint systems)
- ~~`nra/nra_120_unsat_5conic_intersection.smt2`~~ — **FIXED** in 2026-05-25 (verified passing; root cause: pseudoRemainder + multivariate exactDivide (43361cf, 3335d5e)).
- ~~`nra/nra_121_sat_kinematics_orbit.smt2`~~ — **FIXED** in 2026-05-25 (verified passing; root cause: pseudoRemainder + multivariate exactDivide (43361cf, 3335d5e)).
- ~~`nra/nra_122_unsat_3_quadrics_disjoint.smt2`~~ — **FIXED** in 2026-05-25 by Cap. 3 `PolynomialEqualityCombination` + Cap. 1 + Cap. 4 (NRA presolve). The three sphere equalities share high-order row `[1,1,1]`; the left null-space basis `(−1,1,0),(−1,0,1)` yields linear consequences `6x−9=0`, `10y−25=0`; Cap. 1 substitutes `x=3/2, y=5/2` into sphere 1 ⇒ `z²+15/2=0`, whose real-root set is empty ⇒ `DerivedConflict {sphere1, sphere2, sphere3}`. UNSAT.
- ~~`nra/nra_124_sat_robotic_workspace.smt2`~~ — **FIXED** in 2026-05-23 (pseudoRemainder + level-0 projection fix).
- ~~`nra/nra_126_sat_polynomial_lyapunov.smt2`~~ — **FIXED** in 2026-05-25 by Cap. 10 `CandidateModelSearch` (validator-gated). Strategy 10a finds a small-height rational witness on the annulus (e.g. `(x=0, y=1/2)`) and the arithmetic evaluator confirms the three Lyapunov-decrease atoms. Closed by validator-gated SAT witness search, not by complete NRA reasoning.
- ~~`nra/nra_128_sat_geometric_packing.smt2`~~ — **FIXED** in 2026-05-23 (pseudoRemainder + level-0 projection fix).
- ~~`nra/nra_131_sat_brown_2001_relaxed.smt2`~~ — **FIXED** in 2026-05-25 (verified passing; root cause: pseudoRemainder + multivariate exactDivide (43361cf, 3335d5e)).
- ~~`nra/nra_134_unsat_metitarski_negation.smt2`~~ — **FIXED** in 2026-05-25 (verified passing; root cause: pseudoRemainder + multivariate exactDivide (43361cf, 3335d5e)).
- ~~`nra/nra_135_unsat_amzi_classic.smt2`~~ — **FIXED** in 2026-05-24 (multivariate exact-division generalization in GcdEngine).
- ~~`nra/nra_136_sat_amzi_tight.smt2`~~ — **FIXED** in 2026-05-25 by Cap. 10 `CandidateModelSearch` (validator-gated). Strategy 10d's symmetric-diagonal trial with `c=1` yields `(x=y=z=1)`, which the arithmetic evaluator confirms satisfies `x²+y²+z²=3 ≤ 3` and `x+y+z=3 ≥ 3`. Closed by validator-gated SAT witness search, not by complete NRA reasoning.
- ~~`nra/nra_137_unsat_strict_cs_violation.smt2`~~ — **FIXED** in 2026-05-24 (multivariate exact-division generalization in GcdEngine).
- ~~`nra/nra_138_sat_huge_coeff.smt2`~~ — **FIXED** in 2026-05-25 (verified passing; root cause: addTerm canonicalization handles big coefficients (3335d5e)).
- ~~`nia/nia_090_unsat_partition_sum_no_solution.smt2`~~ — **FIXED** in 2026-05-25 by Cap. 11 `NonnegativePolynomialBoundExtractor` + Cap. 4 + Cap. 9. From `x²+y²+z²=13` (each `xᵢ²` manifestly ≥0) Cap. 11 derives `xᵢ²≤13 ⇒ xᵢ∈[−3,3]` (integer √); Cap. 4 intersects with `xᵢ≥1` ⇒ `[1,3]`; Cap. 9 sweeps the `3³=27` candidates — no pairwise-distinct triple sums to 13 (min is `1+4+9=14`) ⇒ `DerivedConflict`. UNSAT.
- ~~`nia/nia_095_unsat_collatz_step_wrong.smt2`~~ — **FIXED** in 2026-05-25 by Cap. 8a `UnconditionalConstantPropagation` + constant-folder bonus path. `n=5` is collected from the top-level unconditional conjunct; substitution into the ITE's arithmetic arguments produces `(mod 5 2) → 1`, `(div 5 2) → 2`, `(+ (* 3 5) 1) → 16` after the arithmetic / relation / boolean constant fold; the guard `(= 1 0)` collapses to `false`; the else branch wins; `n_next = 16` together with `n_next = 8` collapses to `(= 16 8) → false`, which the constant-folder strips into a `ConstBool false` assertion. SAT layer reads `false` → UNSAT.
- ~~`nia/nia_097_unsat_squares_chain.smt2`~~ — **FIXED** in 2026-05-25 by Cap. 1 `AffineSubstitution` (theory-check presolve fixpoint). The unit-coefficient integer-affine equalities `b=a+1`, `c=a+2`, `d=a+3` are substituted into `a·d − b·c`, which collapses to the constant `−2`; the strict atom `a·d > b·c` becomes `−2 > 0` → `DerivedConflict` with reasons `{a·d>b·c, b=a+1, c=a+2, d=a+3}`. UNSAT.
- ~~`nia/nia_098_sat_huge_modulus.smt2`~~ — **FIXED** in 2026-05-24 (ModularConsistencyChecker handles mpz_class moduli of arbitrary size).
- ~~`uflra/uflra_008_sat_array_with_real.smt2`~~ — **FIXED** in 2026-05-25 (verified passing; root cause: frontend purifier improvements (1cedd97)).

### K-batch: SOTA-grade depth findings (2026-05-22)
- ~~`lia/lia_050_sat_sudoku_row.smt2`~~ — **FIXED** in 2026-05-25 (verified passing; root cause: NaryDistinctLowerer expansion (b8bc81f)).
- ~~`ufnra/ufnra_006_sat_circle_fn.smt2`~~ — **FIXED** in 2026-05-25 (verified passing; root cause: frontend purifier + UfInArithPurifier (1cedd97)).
- ~~`ufnra/ufnra_007_unsat_circle_fn_conflict.smt2`~~ — **FIXED** in 2026-05-25 (verified passing; root cause: frontend purifier + UfInArithPurifier (1cedd97)).

### K-batch unsound (high priority)
- ~~`nra/nra_127_sat_swap_compatible.smt2`~~ — **FIXED** in 2026-05-23 (pseudoRemainder + level-0 projection fix). The root cause was the same wrong pseudo-remainder feeding incorrect projection polynomials, leading to unsound unsat. Solver now correctly returns sat.
