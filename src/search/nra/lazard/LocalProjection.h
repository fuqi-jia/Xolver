#pragma once

#include "algebra/poly/RationalPolynomial.h"
#include "search/nra/core/CdcacResult.h"
#include <vector>

namespace xolver {

// ------------------------------------------------------------------
// Resultant of two multivariate polynomials w.r.t. a variable
// ------------------------------------------------------------------
RationalPolynomial resultant(
    const RationalPolynomial& p,
    const RationalPolynomial& q,
    VarId v);

// ------------------------------------------------------------------
// Local projection engine (Collins conservative, local call)
// ------------------------------------------------------------------
// Projection types are declared in CdcacCommon.h and CdcacResult.h

class LocalProjectionEngine {
public:
    /**
     * Local projection: eliminate `eliminateVar` from input polynomials.
     * Uses Collins-style projection (coefficients, discriminant/derivative, pairwise resultants).
     * Carries down polynomials that do NOT contain eliminateVar.
     * Input is deduplicated before processing.
     */
    LocalProjectionResult project(
        const std::vector<ReasonedPolynomial>& input,
        VarId eliminateVar);

private:
    static std::vector<ReasonedPolynomial> normalizeAndDedup(
        const std::vector<ReasonedPolynomial>& input);
};

} // namespace xolver
