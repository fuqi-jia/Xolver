# NRA: replace O(n!) determinant PSC with libpoly `lp_polynomial_psc` — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: superpowers:subagent-driven-development. Steps use checkbox (`- [ ]`) tracking.

**Goal:** Replace the O(n!) recursive `determinant`-based `principalSubresultantCoefficients` (runtime-confirmed #1 NRA bottleneck on projection-bound timeouts like `hong_10`) with libpoly's native `lp_polynomial_psc`, **verdict-preserving** and CAD-equivalent.

**Architecture:** Add a kernel-level `pscChain(PolyId a, PolyId b, VarId v) → vector<PolyId>` wrapping `lp_polynomial_psc`, with correct main-variable handling. Gate the existing free-function `principalSubresultantCoefficients` behind a new default-OFF flag `ZOLVER_NRA_LIBPOLY_PSC`: ON → convert the two RationalPolynomials to PolyId, call `pscChain`, convert the chain back to RationalPolynomial; OFF → the existing determinant (kept verbatim as the **reference oracle**). The determinant is never deleted in this plan — it is the differential test's ground truth.

**Tech Stack:** libpoly (`lp_polynomial_psc`, `lp_polynomial_resultant`), `LibPolyKernel` (owns the `lp_polynomial_context`, VarId↔`lp_variable_t` map), `RationalPolynomial`, GMP, doctest, SMT-LIB2 regression vs z3.

---

## Soundness model (this is the whole point)

This is a **verdict-preserving perf change**. The danger (master): `lp_polynomial_psc` eliminates the libpoly **main (top) variable** per `lp_variable_order`; if `elimVar` isn't the main variable, libpoly eliminates the *wrong* variable → different projection set → shifted cell boundary → **unsound**. So `pscChain` MUST guarantee `v` is the main variable (mirror `LibpolyBackend::projectionPolys`, which already returns `UnsupportedVarOrder` when the var isn't main), and the result must be **CAD-equivalent** to the determinant: the projection *set* identical up to a nonzero rational constant / sign per entry (constants and signs don't change real roots, hence don't change sign-invariant cells).

**Three gates, all hard:**
1. **Differential equivalence (Task 2)** — for many random polynomial pairs, the libpoly psc chain equals the determinant chain *up to a nonzero rational constant per entry* (same index count; entry `i` libpoly = `c_i · det_i`, `c_i ∈ ℚ\{0}`). This catches main-variable / normalization / PSC-indexing bugs directly, without needing a full solve.
2. **Regression OFF == ON (Task 4)** — 633/636 verdicts byte-identical with the flag OFF vs ON. The fast regression cases never hit `budgetExceeded` (small matrices), so the projection set must be identical → 0 verdict changes. **Any** change here is a bug (investigate, do not accept).
3. **z3 differential on a hard sample (Task 4)** — on hong/hycomp/kissing/meti cases, 0 ON-verdict contradicting z3. Cases that were `unknown`/timeout OFF and become decided ON (because libpoly removed the `budgetExceeded` bail) must agree with z3 — those are *recoveries*, reported separately, never contradictions.

**Conversion-churn watch (master):** if Task 4 re-profiling shows per-cell RationalPolynomial↔libpoly conversion now dominates (replacing the determinant cost), that is the signal to escalate to migrating the projection to libpoly's representation throughout (a separate follow-up plan, folding in the RationalPolynomial-efficiency work). Measure, don't assume.

---

## File Structure

```
src/theory/arith/poly/LibPolyKernel.{h,cpp}    MODIFY: add pscChain(PolyId,PolyId,VarId)->vector<PolyId> (+ a RationalPolynomial->PolyId helper if none exists) wrapping lp_polynomial_psc with main-variable handling.
src/theory/arith/nra/projection/SubresultantChain.{h,cpp}  MODIFY: principalSubresultantCoefficients gains a flag branch; needs a kernel handle (add param) for the libpoly path. Determinant kept as the OFF/reference path.
src/theory/arith/nra/projection/ProjectionClosure.{h,cpp}  MODIFY: plumb the PolynomialKernel* through build()/Config into the two principalSubresultantCoefficients call sites.
src/theory/arith/nra/core/CdcacCore.cpp        MODIFY: pass kernel_ into ProjectionClosure::build.
tests/unit/test_nra_libpoly_psc.cpp            NEW: round-trip conversion + psc-vs-determinant differential equivalence.
```

---

### Task 0: Confirm `lp_polynomial_psc` semantics + the RationalPolynomial↔PolyId conversion path

**Files:** none (investigation; record findings in the test file header comment).

- [ ] **Step 1:** Read `/usr/local/include/poly/polynomial.h` around line 303 (`lp_polynomial_psc`): confirm the output array convention (how many entries, ownership/allocation, ordering — index 0 = which subresultant), and that it computes w.r.t. the polynomials' main variable. Read `lp_polynomial_resultant` (296) too. Document the index convention vs. the determinant's `out.psc[j]` (j = 0..n-1, `j`-th principal subresultant coefficient).
- [ ] **Step 2:** Confirm conversion primitives in `LibPolyKernel`: `RationalPolynomial::fromPolyId(PolyId, kernel)` (PolyId→RP, exists). Find or plan the reverse (RationalPolynomial→PolyId): if no helper exists, it is reconstructed from `RationalPolynomial::terms()` via `kernel.mkConst/mkVar/pow/mul/add` after `toPrimitiveInteger()` (libpoly is an integer ring — clear denominators first; a nonzero rational scale is benign for CAD).
- [ ] **Step 3:** Read `LibpolyBackend::projectionPolys` to copy its **main-variable / variable-order** handling (how it ensures `eliminateVar` is the libpoly main variable, and what it does otherwise). `pscChain` must use the same mechanism. Record it.
- [ ] **Step 4:** Report findings (psc index convention, conversion path, main-variable mechanism) before writing code. If `lp_polynomial_psc`'s output cannot be made index-aligned with the determinant's `out.psc`, STOP and report — the equivalence gate depends on a known alignment.

---

### Task 1: `LibPolyKernel::pscChain` (libpoly psc wrapper, main-variable-correct)

**Files:** `LibPolyKernel.{h,cpp}`, `tests/unit/test_nra_libpoly_psc.cpp` (new).

- [ ] **Step 1 (test first):** Write tests for `pscChain(a, b, v)` on small known pairs where the subresultant chain is hand-computable, e.g. `a = x^2 - s`, `b = 2x` (w.r.t. `x`): psc chain entries are known up to constants. Assert the returned PolyIds, converted to RationalPolynomial, match the expected polynomials up to a nonzero rational constant. Include a case where `v` is NOT the natural main variable, asserting `pscChain` still eliminates `v` (or reports unsupported — match the chosen contract).
- [ ] **Step 2:** Run → FAIL (no `pscChain`). `( ulimit -v 2000000; cmake --build build -j2 )`.
- [ ] **Step 3:** Implement `pscChain` in `LibPolyKernel`: convert `a,b` (PolyId, already lp-backed) ensuring `v` is the main variable (per Task 0 Step 3 mechanism); call `lp_polynomial_psc`; wrap each output `lp_polynomial_t*` as a PolyId (`alloc(...)`); free libpoly's array per its ownership contract; return the chain. Degenerate cases (deg_v < 1 on a side) return empty, matching the determinant function's early return.
- [ ] **Step 4:** Build + run the Task 1 tests → PASS. Watch for libpoly memory-ownership mistakes (leak/double-free) — run under the existing test harness which should be clean.
- [ ] **Step 5:** Commit: `feat(nra): LibPolyKernel::pscChain wrapping lp_polynomial_psc (main-variable correct)`. No co-author line.

---

### Task 2: Differential CAD-equivalence oracle (libpoly psc ≡ determinant, up-to-constant)

**Files:** `tests/unit/test_nra_libpoly_psc.cpp` (append). This is the soundness keystone.

- [ ] **Step 1 (test):** Write a randomized differential test: generate N≈300 random bivariate/trivariate RationalPolynomial pairs `(p,q)` over a small integer-coefficient grid, modest degrees (so the determinant is affordable and exercised). For each, w.r.t. each shared variable `v`: compute `det = principalSubresultantCoefficients(p,q,v,maxDim)` (determinant path, the reference) and `lib = ` the libpoly path (convert→pscChain→convert back). Assert: (a) `det.psc.size() == lib.size()` (when neither bails on budget), and (b) for each index `i`, `lib[i]` and `det.psc[i]` are equal **up to a nonzero rational constant** (i.e. `lib[i]` is zero iff `det.psc[i]` is zero, and otherwise `lib[i] * det.psc[i].someCoeff == det.psc[i] * lib[i].someCoeff` — implement an `equalUpToRationalScale(RationalPolynomial, RationalPolynomial)` helper: normalize both to primitive-integer + positive leading sign, then compare for exact equality).
- [ ] **Step 2:** Run → FAIL (oracle helper / wiring missing). Build.
- [ ] **Step 3:** Implement `equalUpToRationalScale` (test-local). Use the existing `RationalPolynomial::normalize()`/`toPrimitiveInteger()` to canonicalize, fix the sign by the leading coefficient, compare term maps for equality.
- [ ] **Step 4:** Run → PASS for all N pairs. **If any pair fails**, the libpoly path is NOT CAD-equivalent (likely a main-variable or index-alignment bug) — STOP, fix `pscChain`, do not proceed. This is the gate that prevents the unsound projection-set shift.
- [ ] **Step 5:** Commit: `test(nra): differential CAD-equivalence — libpoly psc ≡ determinant up to rational scale`. No co-author line.

---

### Task 3: Gate `principalSubresultantCoefficients` behind `ZOLVER_NRA_LIBPOLY_PSC`

**Files:** `SubresultantChain.{h,cpp}`, `ProjectionClosure.{h,cpp}`, `CdcacCore.cpp`.

- [ ] **Step 1 (test):** Add a test that the gated path produces the same `out.psc` (up to rational scale) as the determinant on a fixed pair, toggling the env var — mirrors Task 2 but through the public `principalSubresultantCoefficients` entry the projection actually calls.
- [ ] **Step 2:** Plumb a `const PolynomialKernel* kernel` into `principalSubresultantCoefficients` (new param; the two `ProjectionClosure` call sites pass it; `ProjectionClosure::build` receives it from `CdcacCore` which has `kernel_`). When the kernel is null or the flag is OFF → determinant path (byte-identical to today). When ON and kernel present → convert `p,q`→PolyId, call `kernel->pscChain`, convert chain back to RationalPolynomial, `normalize()` each, fill `out.psc`. Preserve `budgetExceeded` semantics: the libpoly path does not bound matrix dim, so it never sets `budgetExceeded` (this is the recovery source — note it).
- [ ] **Step 3:** Read the flag once (env `ZOLVER_NRA_LIBPOLY_PSC`), same idiom as `ZOLVER_NRA_VARORDER_SIMPLEX`.
- [ ] **Step 4:** Build; run the new gated test + the full `CDCAC*`/`P2b*` projection unit groups (flag OFF → unchanged). PASS.
- [ ] **Step 5:** Commit: `feat(nra): route principalSubresultantCoefficients through libpoly psc behind ZOLVER_NRA_LIBPOLY_PSC (default off)`. No co-author line.

---

### Task 4: Validation + promotion + churn measurement

**Files:** none (measurement; append a results block to this plan).

- [ ] **Step 1:** Unit suite (flag OFF) green; record count.
- [ ] **Step 2:** Regression OFF: `( ulimit -v 2000000; python3 tools/run_regression.py --root tests/regression --solver build/bin/zolver --timeout 20 -j 2 )` → baseline (636/636 or current), 0 UNSOUND.
- [ ] **Step 3:** Regression ON (`ZOLVER_NRA_LIBPOLY_PSC=1`): MUST be **byte-identical verdicts** to OFF (gate 2). Any change = bug → STOP.
- [ ] **Step 4:** z3 differential on a hard sample (the families with timeouts): for ~30 cases each from `hong`, `hycomp`, `kissing`, `meti-tarski` (benchmark at `/mnt/d/D_Study/BUAA/projects/NLColver/benchmark/non-incremental/QF_NRA`), compare OFF vs ON vs z3. Classify recoveries (unknown/timeout→decided==z3) and require **0 contradictions** (ON vs z3).
- [ ] **Step 5:** Re-profile `hong_10` + `hycomp/ball_count_…global_10` with the flag ON (gdb launch-under sampler, per [[nra-benchmarks-and-wsl-profiling]]): confirm `(anonymous namespace)::determinant` is GONE from the profile, and report the new hot path. If RationalPolynomial↔libpoly conversion now dominates → record it as the trigger for the projection-migration follow-up.
- [ ] **Step 6:** Append results block (counts, recoveries, 0-unsound/0-contradiction confirmation, new profile, churn verdict, promotion decision). Promotion: since it's verdict-preserving with strictly-better completeness (no budget bail), this flag is a strong default-ON candidate once gates 1–3 are clean — recommend to master with the panda2 A/B. Commit the results.

---

## Self-Review
- The determinant is retained as the OFF path AND the differential oracle — equivalence is verified directly (Task 2), not assumed.
- The one unsound failure mode (wrong eliminated variable) is addressed structurally (main-variable handling, Task 1) and caught empirically (Task 2 + gate 2).
- `budgetExceeded` removal is a *recovery* (more complete projection), validated against z3 (gate 3) — never a contradiction.
- Conversion churn is measured (Task 4 Step 5), with a defined escalation path, not pre-optimized.
- Flag default-OFF; OFF path byte-identical; promotion gated on the three hard checks + panda2 A/B.
