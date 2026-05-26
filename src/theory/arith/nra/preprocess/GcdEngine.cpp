#include "theory/arith/nra/preprocess/GcdEngine.h"
#include "theory/arith/nra/preprocess/SubresultantEngine.h"
#include <optional>

namespace zolver {

// Forward declaration for mutual recursion.
static std::optional<RationalPolynomial> tryExactDivideByVar(
    const RationalPolynomial& p,
    const RationalPolynomial& g,
    VarId var);

// Recursive multivariate exact division.
//   Computes Q such that p == g * Q exactly in Q[X], returning nullopt if no
//   such polynomial exists (i.e. g does not divide p).
//   Terminates because each recursion level fixes a variable v in g and
//   forwards to tryExactDivideByVar, whose inner divisions are on the
//   coefficients of g w.r.t. v — polynomials in strictly fewer variables.
static std::optional<RationalPolynomial> polyExactDivide(
    const RationalPolynomial& p,
    const RationalPolynomial& g) {

    if (g.isZero()) return std::nullopt;
    if (p.isZero()) return RationalPolynomial::fromConstant(mpq_class(0));

    // Base case: divisor is a non-zero rational constant. Scale p by 1/g.
    if (g.isConstant()) {
        mpq_class gVal = g.constantValue();
        if (gVal == 0) return std::nullopt;
        return p * RationalPolynomial::fromConstant(mpq_class(1) / gVal);
    }

    // Recursive case: pick any variable that g actually depends on. The
    // returned variable set is non-empty here because g is not constant.
    auto gVars = g.variables();
    VarId v = *gVars.begin();
    return tryExactDivideByVar(p, g, v);
}

// Exact polynomial division of `p` by `g` viewing both as polynomials in
// the main variable `var` with coefficients in Q[other_vars].
//
// Differences from the previous implementation:
//   * `lc(g)` is allowed to be a polynomial in other variables, not just a
//     rational constant — divisions of coefficients by lc(g) are delegated
//     to `polyExactDivide`, which recurses on the structure of `lc(g)`.
//     This makes the routine a complete multivariate exact-division
//     algorithm: it succeeds iff `g` truly divides `p` in Q[X].
//   * Lifting it past the old constant-lc(g) restriction was necessary
//     for cases like x²y² ÷ (2x²y) = (1/2)y (nra_112's squarefree
//     extraction). The old short-circuit caused `gcdCandidateBySubresultant`
//     to report `ExactDivisionFailed`, which propagated to
//     LocalProjectionEngine as a `hasDegeneracy` flag and finally to
//     CdcacCore as the "no local polys" sample-only fallback.
static std::optional<RationalPolynomial> tryExactDivideByVar(
    const RationalPolynomial& p,
    const RationalPolynomial& g,
    VarId var) {

    int degP = p.degree(var);
    int degG = g.degree(var);

    if (degG < 0) return std::nullopt;
    if (degP < degG) {
        // p has lower degree in var than g; the only way g divides p is if
        // p is zero (handled by the caller) or g is constant in var (degG = 0,
        // covered by the polyExactDivide constant base case before recursing).
        return std::nullopt;
    }

    auto pCoeffs = p.coefficients(var);
    auto gCoeffs = g.coefficients(var);
    const RationalPolynomial& lcG = gCoeffs[degG];

    int quotDeg = degP - degG;
    std::vector<RationalPolynomial> quotCoeffs(quotDeg + 1);

    for (int i = quotDeg; i >= 0; --i) {
        const RationalPolynomial& leadCoeff = pCoeffs[i + degG];
        // Exact-divide the current leading coefficient by lc(g) over the
        // coefficient ring Q[other_vars]. If the division leaves a remainder,
        // g does not divide p exactly and we abort.
        auto qOpt = polyExactDivide(leadCoeff, lcG);
        if (!qOpt) return std::nullopt;
        quotCoeffs[i] = std::move(*qOpt);

        // Subtract quotCoeffs[i] * g * var^i from the running remainder
        // (represented as pCoeffs).
        for (int j = 0; j <= degG; ++j) {
            pCoeffs[i + j] = pCoeffs[i + j] - quotCoeffs[i] * gCoeffs[j];
        }
    }

    // The running remainder must have degree < degG in var for an exact
    // division. Check that all low-degree coefficients are zero.
    for (int i = 0; i < degG; ++i) {
        if (!pCoeffs[i].isZero()) {
            return std::nullopt;
        }
    }

    // Reconstruct quotient polynomial. addTerm canonicalizes the resulting
    // MonomialKey, so we can append {var, i} unconditionally; the i == 0
    // case (var^0 = 1) will be dropped during canonicalization.
    RationalPolynomial result;
    for (int i = 0; i <= quotDeg; ++i) {
        if (quotCoeffs[i].isZero()) continue;
        for (const auto& [key, coeff] : quotCoeffs[i].terms()) {
            MonomialKey newKey = key;
            newKey.push_back({var, i});
            result.addTerm(newKey, coeff);
        }
    }
    result.normalize();
    return result;
}

// Public-style wrapper preserving the original (p, g, var) entry point used by
// the rest of GcdEngine. Forwards to the recursive routine; callers that
// don't have a meaningful "main variable" should use `polyExactDivide`.
static std::optional<RationalPolynomial> tryExactDivide(
    const RationalPolynomial& p,
    const RationalPolynomial& g,
    VarId var) {
    return tryExactDivideByVar(p, g, var);
}

GcdEngine::Result GcdEngine::gcdCandidateBySubresultant(
    const RationalPolynomial& p,
    const RationalPolynomial& q,
    VarId var) {

    Result result;

    // Step 1: Primitive part w.r.t. var
    RationalPolynomial ppP = p.primitivePart(var);
    RationalPolynomial ppQ = q.primitivePart(var);

    // Step 2: Subresultant PRS
    auto prs = SubresultantEngine::run(ppP, ppQ, var);
    result.hasParametricDegreeDrop = prs.hasParametricDegreeDrop;

    RationalPolynomial g = prs.gcdCandidate;
    if (g.isZero()) {
        result.reason = CdcacUnknownReason::GcdFailed;
        return result;
    }

    // Make g primitive as well
    g = g.primitivePart(var);

    // Step 3 & 4: Mandatory exactDivide verification
    auto pQuotOpt = tryExactDivide(p, g, var);
    auto qQuotOpt = tryExactDivide(q, g, var);

    if (!pQuotOpt || !qQuotOpt) {
        result.reason = CdcacUnknownReason::ExactDivisionFailed;
        return result;
    }

    // Verify by multiplication
    RationalPolynomial pCheck = g * *pQuotOpt;
    RationalPolynomial qCheck = g * *qQuotOpt;

    // Compare term by term (using normalized forms)
    pCheck.normalize();
    qCheck.normalize();
    
    RationalPolynomial pNorm = p;
    pNorm.normalize();
    RationalPolynomial qNorm = q;
    qNorm.normalize();

    if (pCheck.terms() != pNorm.terms() || qCheck.terms() != qNorm.terms()) {
        result.reason = CdcacUnknownReason::ExactDivisionFailed;
        return result;
    }

    result.gcd = g;
    result.pQuot = *pQuotOpt;
    result.qQuot = *qQuotOpt;
    result.exact = true;
    return result;
}

std::optional<RationalPolynomial> GcdEngine::exactDivide(
    const RationalPolynomial& p, const RationalPolynomial& g) {
    return polyExactDivide(p, g);
}

} // namespace zolver
