#pragma once

#include "theory/arith/kernel/poly/RationalPolynomial.h"
#include "theory/arith/logics/nra/core/CdcacTypes.h"
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
// PolyRole, ReasonedPolynomial, LocalProjectionResult are now defined in CdcacTypes.h

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
