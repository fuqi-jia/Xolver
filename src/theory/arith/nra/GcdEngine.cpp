#include "theory/arith/nra/GcdEngine.h"
#include "theory/arith/nra/SubresultantEngine.h"
#include <optional>

namespace nlcolver {

// Helper: attempt exact division of p by g w.r.t. var.
// Returns nullopt if division is not exact or lc(g) is not constant.
static std::optional<RationalPolynomial> tryExactDivide(
    const RationalPolynomial& p,
    const RationalPolynomial& g,
    VarId var) {

    int degP = p.degree(var);
    int degG = g.degree(var);

    if (degG < 0) return std::nullopt;
    if (degP < degG) return std::nullopt;

    auto pCoeffs = p.coefficients(var);
    auto gCoeffs = g.coefficients(var);

    RationalPolynomial lcG = gCoeffs[degG];
    if (!lcG.isConstant()) {
        // V2-4: non-constant leading coefficient requires recursive exact division.
        // For now, return nullopt (candidate not verifiable).
        return std::nullopt;
    }

    mpq_class lcGval = lcG.constantValue();
    if (lcGval == 0) return std::nullopt;

    int quotDeg = degP - degG;
    std::vector<RationalPolynomial> quotCoeffs(quotDeg + 1);

    for (int i = quotDeg; i >= 0; --i) {
        RationalPolynomial leadCoeff = pCoeffs[i + degG];
        if (!leadCoeff.isConstant()) {
            return std::nullopt;
        }
        mpq_class qVal = leadCoeff.constantValue() / lcGval;
        quotCoeffs[i] = RationalPolynomial::fromConstant(qVal);

        for (int j = 0; j <= degG; ++j) {
            pCoeffs[i + j] = pCoeffs[i + j] - quotCoeffs[i] * gCoeffs[j];
        }
    }

    // Check remainder is zero
    for (int i = 0; i < degG; ++i) {
        if (!pCoeffs[i].isZero()) {
            return std::nullopt;
        }
    }

    // Reconstruct quotient polynomial
    RationalPolynomial result;
    for (int i = 0; i <= quotDeg; ++i) {
        if (quotCoeffs[i].isZero()) continue;
        for (const auto& [key, coeff] : quotCoeffs[i].terms()) {
            MonomialKey newKey = key;
            auto it = std::lower_bound(newKey.begin(), newKey.end(), var,
                [](const auto& pair, VarId vid) { return pair.first < vid; });
            newKey.insert(it, {var, i});
            result.addTerm(newKey, coeff);
        }
    }
    result.normalize();
    return result;
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

} // namespace nlcolver
