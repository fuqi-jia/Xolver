// src/theory/arith/logics/nra/simplex/NraLinearExtractor.h
#pragma once
#include "ir/types.h"
#include "algebra/poly/PolynomialKernel.h"
#include "search/nra/core/CdcacTypes.h"      // CdcacCommon types (ConstraintId, ModelSeed, ...)
#include "search/nra/core/CdcacConstraint.h" // CdcacConstraint, Relation, SatLit
#include <gmpxx.h>
#include <vector>

namespace xolver {

// One linear atom: (sum coeffs[i].second * coeffs[i].first) + constant  rel  0
struct LinearAtom {
    std::vector<std::pair<VarId, mpq_class>> coeffs;
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

// Replace each distinct monomial with an independent real variable. IDs are
// local to this result, not kernel variables. Every polynomial model induces a
// model of this relaxation; only its UNSAT direction can decide the input.
// Unrepresentable constraints are omitted, which only weakens the relaxation.
std::vector<LinearAtom> linearizeMonomials(
    const PolynomialKernel& kernel,
    const std::vector<CdcacConstraint>& constraints);

} // namespace xolver
