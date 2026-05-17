#pragma once

#include "theory/arith/poly/RationalPolynomial.h"
#include "theory/arith/nra/CdcacTypes.h"
#include <vector>

namespace nlcolver {

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
enum class PolyRole {
    ConstraintPolynomial,
    ProjectionPolynomial,
    BoundaryPolynomial,
    DelineationPolynomial
};

struct ReasonedPolynomial {
    RationalPolynomial poly;
    PolyRole role;
    std::vector<SatLit> reasons;
};

struct LocalProjectionResult {
    bool hasDegeneracy = false;
    std::vector<ReasonedPolynomial> polys;
    CdcacUnknownReason degeneracyReason = CdcacUnknownReason::None;
};

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

} // namespace nlcolver
