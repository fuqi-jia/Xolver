#pragma once

#include "theory/arith/nra/core/CdcacTypes.h"
#include "theory/arith/nra/projection/LocalProjection.h"
#include <vector>

namespace nlcolver {

/**
 * DegeneracyResolver: resolve zero resultant degeneracy in local projection.
 *
 * Two cases:
 * 1. Self-degeneracy: resultant(p, p') = 0  →  p is not squarefree.
 *    Resolution: replace p with p / gcd(p, p') if exactDivide succeeds.
 * 2. Pair-degeneracy: resultant(p, q) = 0  →  p and q share a common factor.
 *    Resolution: extract common factor g = gcd(p, q) and add to projection set.
 *
 * V2-5: only resolves when exactDivide verification succeeds.
 * Unresolved degeneracy → hasUnresolvedDegeneracy = true.
 */
struct DegeneracyResolverConfig {
    int maxResolutionDepth = 3;
    int maxGeneratedPolys = 128;
};

class DegeneracyResolver {
public:
    struct Resolution {
        std::vector<ReasonedPolynomial> replacementPolys;
        bool hasUnresolvedDegeneracy = false;
        CdcacUnknownReason reason = CdcacUnknownReason::None;
    };

    explicit DegeneracyResolver(DegeneracyResolverConfig cfg = {});

    /**
     * Resolve self-degeneracy: resultant(p, p') = 0.
     * Returns replacement polynomials (squarefree part) or empty if unresolved.
     */
    Resolution resolveSelfDegeneracy(
        const ReasonedPolynomial& rp,
        VarId eliminateVar);

    /**
     * Resolve pair-degeneracy: resultant(p, q) = 0.
     * Returns replacement polynomials (common factor + reduced pair) or empty if unresolved.
     */
    Resolution resolvePairDegeneracy(
        const ReasonedPolynomial& rp1,
        const ReasonedPolynomial& rp2,
        VarId eliminateVar);

private:
    DegeneracyResolverConfig cfg_;
};

} // namespace nlcolver
