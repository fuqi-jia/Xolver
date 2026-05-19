#include "theory/arith/nra/preprocess/DegeneracyResolver.h"
#include "theory/arith/nra/preprocess/GcdEngine.h"

namespace nlcolver {

DegeneracyResolver::DegeneracyResolver(DegeneracyResolverConfig cfg)
    : cfg_(cfg) {}

DegeneracyResolver::Resolution DegeneracyResolver::resolveSelfDegeneracy(
    const ReasonedPolynomial& rp,
    VarId eliminateVar) {

    Resolution res;
    const auto& p = rp.poly;

    if (p.isZero() || p.isConstant()) {
        return res;
    }

    auto dp = p.derivative(eliminateVar);
    if (dp.isZero()) {
        // p' = 0: p is constant w.r.t. eliminateVar or p = c*(v)^k
        // No self-degeneracy to resolve
        return res;
    }

    // Compute gcd(p, p')
    auto gcdResult = GcdEngine::gcdCandidateBySubresultant(p, dp, eliminateVar);
    if (!gcdResult.exact) {
        res.hasUnresolvedDegeneracy = true;
        res.reason = gcdResult.reason;
        return res;
    }

    if (gcdResult.gcd.isConstant()) {
        // Already squarefree (gcd is constant)
        return res;
    }

    // squarefree = p / gcd
    RationalPolynomial squarefree = gcdResult.pQuot;
    if (!squarefree.isZero()) {
        res.replacementPolys.push_back({
            squarefree,
            PolyRole::ProjectionPolynomial,
            rp.reasons
        });
    }

    return res;
}

DegeneracyResolver::Resolution DegeneracyResolver::resolvePairDegeneracy(
    const ReasonedPolynomial& rp1,
    const ReasonedPolynomial& rp2,
    VarId eliminateVar) {

    Resolution res;
    const auto& p = rp1.poly;
    const auto& q = rp2.poly;

    if (p.isZero() || q.isZero() || p.isConstant() || q.isConstant()) {
        return res;
    }

    // Compute gcd(p, q)
    auto gcdResult = GcdEngine::gcdCandidateBySubresultant(p, q, eliminateVar);
    if (!gcdResult.exact) {
        res.hasUnresolvedDegeneracy = true;
        res.reason = gcdResult.reason;
        return res;
    }

    if (gcdResult.gcd.isConstant()) {
        // No common factor
        return res;
    }

    // Add common factor to projection set
    std::vector<SatLit> mergedReasons = rp1.reasons;
    mergedReasons.insert(mergedReasons.end(), rp2.reasons.begin(), rp2.reasons.end());
    std::sort(mergedReasons.begin(), mergedReasons.end(),
        [](SatLit a, SatLit b) {
            if (a.var != b.var) return a.var < b.var;
            return a.sign < b.sign;
        });
    mergedReasons.erase(std::unique(mergedReasons.begin(), mergedReasons.end(),
        [](SatLit a, SatLit b) {
            return a.var == b.var && a.sign == b.sign;
        }), mergedReasons.end());

    res.replacementPolys.push_back({
        gcdResult.gcd,
        PolyRole::ProjectionPolynomial,
        mergedReasons
    });

    return res;
}

} // namespace nlcolver
