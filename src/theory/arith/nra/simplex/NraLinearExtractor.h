// src/theory/arith/nra/simplex/NraLinearExtractor.h
#pragma once
#include "expr/types.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include "theory/arith/nra/core/CdcacTypes.h"      // CdcacCommon types (ConstraintId, ModelSeed, ...)
#include "theory/arith/nra/core/CdcacConstraint.h" // CdcacConstraint, Relation, SatLit
#include <gmpxx.h>
#include <vector>

namespace zolver {

// One linear atom: (sum coeffs[i].second * coeffs[i].first) + constant  rel  0
struct LinearAtom {
    std::vector<std::pair<VarId, mpq_class>> coeffs; // degree-1 monomials
    mpq_class constant{0};                           // the powers-empty monomial
    Relation rel;
    SatLit reason;
};

struct ClassifiedConstraints {
    std::vector<LinearAtom> linear;          // every monomial has total degree <= 1
    std::vector<CdcacConstraint> nonlinear;  // at least one monomial of total degree >= 2
};

// Classify via kernel->terms(). A constraint whose terms() is nullopt
// (non-integer coeffs / unsupported) is treated as nonlinear (conservative).
ClassifiedConstraints classifyConstraints(
    const PolynomialKernel& kernel,
    const std::vector<CdcacConstraint>& constraints);

} // namespace zolver
