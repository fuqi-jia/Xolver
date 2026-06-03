# Lazard Method for CDCAC — Hardened Design Contracts

Status: design pinned (pre-implementation). Selected representation: **algebraic-coefficient towers**.
Gated behind `--nra-projection=lazard` (default stays `collins-safe`). This file is the
binding contract; modules below MUST conform. Reviewer-mandated hardenings are marked **[H1]..[H7]**.

## Binding invariant

- **SAT** ⇐ only a full assignment that exactly validates all original active constraints.
- **UNSAT** ⇐ only a Lazard-projection-certified covering; every conflict cell carries a
  `LazardCellCertificate` proving: closure complete ∧ prefix cell complete ∧ Lazard valuation
  complete ∧ root isolation/merge complete ∧ `FullLineReason` legal.
- Any projection / valuation / root / certificate step incomplete ⇒ **Unknown, never UNSAT**.

---

## [H1] Tower kernel canonical representation (`valuation/TowerAlgebraicKernel`)

The kernel does **NOT** represent a tower element as "one `RealAlg` per coefficient". It represents
elements of the field tower

```
ℚ(α₀, …, α_{k-1})  ≅  ℚ[A₀, …, A_{k-1}] / ⟨ m₀(A₀), m₁(A₀,A₁), …, m_{k-1}(A₀,…,A_{k-1}) ⟩
```

where `Aᵢ` are fresh *extension variables* and `mᵢ` is the (monic, over the lower tower) minimal
polynomial of generator `αᵢ`. Concretely:

```cpp
struct TowerContext {
    std::vector<VarId>            extensionVars;   // A0, A1, ... (fresh, distinct from problem vars)
    std::vector<RealAlg>          generators;      // α0, α1, ... (each pins the real embedding + interval)
    std::vector<RationalPolynomial> definingPolys; // m_i in extensionVars[0..i]; reduced, leading-monic
    ProjectionClosureId           closureId;       // [H7] which closure this tower belongs to
    std::vector<CellId>           prefixCells;      // [H7] prefix cell chain that built this tower
};

struct TowerElement {
    RationalPolynomial numerator;     // in extensionVars only; ALWAYS kept reduced (see below)
    RationalPolynomial denominator;   // v1: MUST be the constant 1 (see denominator rule)
    const TowerContext* ctx;
};

struct AlgebraicCoeffUnivariate {
    VarId mainVar;                    // the target lift variable x_k
    std::vector<TowerElement> coeffs; // coeffs[i] = coeff of mainVar^i; coeffs.back() != 0 after reduce
    const TowerContext* ctx;
};
```

**Canonicalization / reduction (mandatory, exact):** a `TowerElement.numerator` is *reduced* iff it is
the normal form modulo `⟨m₀,…,m_{k-1}⟩` — i.e. for each `Aᵢ` its degree is `< deg(mᵢ)`. Reduction is
performed by exact multivariate pseudo-division by each `mᵢ` (highest generator first), reusing
`RationalPolynomial::pseudoRemainder` + the tower's leading-monic `mᵢ` so no spurious denominators
appear. Every constructor and every `+ − ×` result MUST end reduced.

**Exact zero-test:** `isZeroExact(TowerElement e)` ≡ `reduce(e.numerator).isZero()`. This is a decision
procedure (not interval-based). Interval arithmetic on `generators` is permitted ONLY to *witness*
sign/ordering for root isolation **after** an exact zero/nonzero decision — never to *prove* zero.

**Denominator rule (v1):** `TowerElement` is a **polynomial** element only (`denominator == 1`). Any op
that would require true field division (inverting a tower element) returns
`LazardIncompleteReason::AlgebraicCoefficientUnsupported` ⇒ the enclosing cell is incomplete ⇒ Unknown.
**Lazard valuation (derivative/specialization) MUST NOT depend on uncontrolled division.** (A later v2
may add a reduced fraction representation with a proven-nonzero denominator; out of scope now.)

Underlying scalar arithmetic on generators may use libpoly's `lp_algebraic_number` *arithmetic/sign*
(stable) — but NEVER `lp_polynomial_roots_isolate` under an assignment (the known SIGSEGV).

---

## [H2] Norm candidate + exact filter contract (`valuation/TowerRootIsolation`)

`isolateRealRootsInTower(AlgebraicCoeffUnivariate F, prefix)` is two-stage and the filter is a
**decision**, not an approximation:

1. **Candidate generation (superset).** Form the Norm `N(x) ∈ ℚ[x]` by iterated resultant eliminating
   every extension variable `Aᵢ` from `F` against the defining polynomials `mᵢ` (extends
   `isolateRealRootsViaNorm`). Isolate the real roots of `N` over ℚ. These are **candidates only** —
   `N`'s roots include all conjugate/extraneous branches.
2. **Exact filter (mandatory).** For each candidate `β`: adjoin `β` to the tower to form
   `ℚ(α₀,…,α_{k-1}, β)` and **exact-test `F(β) = 0`** via `isZeroExact` in the extended tower. Keep `β`
   iff the test returns *exactly zero*.
   - Extraneous/conjugate `β` that fail the test **MUST be deleted** — they are not cell boundaries.
   - If the exact test is **inconclusive** for any candidate (unsupported op / budget) ⇒
     `TowerRootIsolationUnsupported` ⇒ Unknown. Never keep an unfiltered candidate set.

Decisive examples this contract must satisfy: `x=√2, F(y)=y−x` ⇒ `N=y²−2`, candidates `±√2`, **only
`+√2` survives**; and `x=√2` vs `x=−√2` on the same `F` ⇒ **different** surviving root.

---

## [H3] Lazard valuation derivative-order replay contract (`valuation/LazardValuationEngine`)

`evaluateToUnivariate(p, prefixChain, targetVar)` recovers nullification via a **derivative-order
witness**, and this is a contract on the *engine*, not only the debug validator:

```
for each prefix coord (xi = ai), in variable order:
  for r = 0 .. deg_xi(q):
    s = specializeVarToAlgebraic( ∂^r q / ∂xi^r , xi = ai )      # exact, tower-aware
    if !isZeroExact(s): { multiplicity m := r; q := normalize(s); break }
  if no nonzero found: return Incomplete(ValuationAllDerivativesZero)
```

- The residual is the Lazard residual **up to the nonzero rational factor `1/r!`**, which is harmless
  for roots and sign after `normalize`. The engine MUST record, per step, `{var, sample, multiplicity m,
  derivativeOrder=m, normalizationPolicy}` in a `LazardValuationTrace`.
- **Contract (enforced, not just asserted in debug):** for the chosen `m`, `∂^r` specializes to **exact
  zero** for all `r < m` and to **exact nonzero** at `r = m`. The implementation establishes this by
  construction (the loop), and the trace records enough to replay it.
- The engine MUST be derivative-based throughout — **never** mix in pseudo-division so that provenance
  stays replayable. `normalizationPolicy` (drop the `1/r!` / unit-normalize) is fixed once and recorded.

`specializeToUnivariate` (ordinary, rational-prefix) appears in the Lazard lift path **only** as the
recorded special case `multiplicity = 0` over a rational coordinate; otherwise the tower-aware
`specializeVarToAlgebraic` is used.

---

## [H4] Multivariate squarefree / content / primitive part (`projection/Squarefree`)

Lazard projection operates on the **primitive squarefree basis w.r.t. the eliminated variable**.
Definitions (all w.r.t. an explicit `VarId v`, coefficients in `ℚ[lower vars]`):

```
content_v(p)       = gcd over ℚ[lower vars] of the coefficients of p viewed as univariate in v
primitivePart_v(p) = p / content_v(p)
squarefreePart_v(p)= primitivePart_v(p) / gcd_v( primitivePart_v(p), ∂/∂v primitivePart_v(p) )
```

Implementation builds on `GcdEngine::gcdCandidateBySubresultant(p,q,v)` (subresultant PRS + mandatory
exactDivide verification). The existing `RationalPolynomial::content/primitivePart` (which return 1 for
multivariate coefficients) are **insufficient** and must NOT be used for the basis.

**Required unit tests (gate before the operator is trusted):**
`x²−y²` wrt x squarefree; `(x−y)²` wrt x ⇒ squarefreePart `x−y`; `y(x+1)²` wrt x ⇒ squarefreePart
`x+1`; `content_x(y·x+y)=y`; `primitivePart_x(y·x+y)=x+1`. Degenerate: zero derivative, degree-0,
content 0/1.

---

## [H5] `FullLineReason` = complete proof of irrelevance

```cpp
enum class FullLineReason { CompleteLazardEvaluationNoRoots, NoRelevantPolys, IncompleteProjectionFallback };
```

A `FullLine` cell may back UNSAT **only** when (all hold): closure complete ∧ prefix cell complete ∧
**every** conflict-support poly relevant to this level was Lazard-evaluated to completion ∧ none
nullified without valuation recovery ∧ all evaluated univariates are constant or genuinely real-root-free
∧ root isolation complete. `NoRelevantPolys` is a *complete proof of irrelevance*, **not**
`closure.levelPolys[k].empty()` and **not** `allRoots.empty()` (those can also arise from incompleteness).
Anything short ⇒ `IncompleteProjectionFallback` ⇒ Unknown.

---

## [H6] `checkFullSample` three-way (KEEP — already correct)

1. full assignment satisfies all active original constraints ⇒ **SAT** (+ model);
2. some constraint violated at the full sample ⇒ a **leaf cell** routed up through covering + per-cell
   gate — **never** a direct CDCL conflict from the failing sample;
3. only a **prefix-independent constant** contradiction (`0>0`, `0=1`, `0≠0`) ⇒ direct theory conflict.

---

## [H7] Provenance hooks reserved from step A

`LazardProjectionClosure` + `LazardProjectionSource` (built first, in step A) MUST already carry the
fields the later tower/valuation/certificate layers consume, so the operator is not an isolated shell:

```cpp
using ProjectionClosureId = uint32_t;   // fingerprint( active polys + var order + mode + EC policy + budget + norm version )

enum class LazardProjectionOpKind : uint8_t {
    InputPolynomial, Content, PrimitivePart, SquarefreeFactor,
    LeadingCoefficient, TrailingCoefficient, Discriminant, Resultant
};
struct LazardProjectionSource {
    LazardProjectionOpKind op;
    int output;                       // entry index in the closure
    int parent1; int parent2;         // -1 if unary
    VarId eliminatedVar;
};

struct LazardCellCertificate {
    ProjectionClosureId closureId;
    CellId              prefixCellId;
    bool closureComplete, prefixComplete, valuationComplete,
         rootIsolationComplete, rootMergeComplete;
    std::vector<ValuationTraceId> evaluatedPolys;   // → LazardValuationTrace
    RootSetFingerprint            rootSet;          // closureId+prefixCellId+targetVar+eval ids+root ids+order
    std::optional<FullLineReason> fullLineReason;
};

enum class LazardIncompleteReason : uint8_t {
    None,
    ProjectionKernelFailure, ProjectionBudgetExceeded,
    ValuationAllDerivativesZero,
    AlgebraicCoefficientUnsupported, AlgebraicZeroCheckFailed,
    TowerRootIsolationUnsupported,
    RootComparisonInconclusive,
    ProjectionReplayFailed, ValuationReplayFailed,
    PrefixCertificateIncomplete
};
```

The closure caches on `closureId`; never reuse across a different active assignment.

---

## Equational constraints

Default `--nra-lazard-ec-reduction=off`: all active polynomials enter as sign-invariance support. The
`LazardECPolicy{Disabled, SingleDesignatedEC, RecursiveEC}` enum is reserved; any non-`Disabled` mode
must add curtain/valuation-invariance obligations + replay before a cell may be
`builtFromCompleteProjection`.

## Build order

A (Squarefree + LazardProjectionOperator + LazardProjectionClosure, **with [H7] hooks**, pure-algebra
unit tests) → B (TowerAlgebraicKernel [H1] + TowerRootIsolation [H2]) → C (LazardValuationEngine [H3]) →
D (LazardLifter + LazardCellCertificate + per-cell gate [H5]) → E (CdcacCore wiring + [H6] + replay
validator) → F (verification + Collins-vs-Lazard differential + 7-way breakdown).

## Acceptance (Lazard mode)

`ctest` green; regression false_sat = 0, false_unsat = 0; **nra_129 must be UNSAT in lazard mode**
(tower/algebraic-prefix lifting is what closes it — a tower-unsupported Unknown means Lazard is *not*
done, even though it's behind the flag); collins-safe default never regresses; every lazard UNSAT
passes the per-cell gate with projection-source + valuation-trace + root-certificate; Collins-vs-Lazard
decided verdicts never disagree. Required tower tests: Norm extraneous-root filter, degree drop,
ordinary-nullification recovery, two-generator tower `√√2`, same-Norm-different-branch.
```
