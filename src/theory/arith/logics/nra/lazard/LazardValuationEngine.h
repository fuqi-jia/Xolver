#pragma once

#include "theory/arith/kernel/poly/RationalPolynomial.h"
#include "theory/arith/logics/nra/lazard/TowerAlgebraicKernel.h"
#include "expr/types.h"
#include <vector>

namespace xolver {

// ---------------------------------------------------------------------------
// LazardValuationEngine (step C, LAZARD.md [H3]) — evaluate a polynomial at a
// tower prefix to a univariate in the lift variable, with derivative-order
// nullification recovery.
//
// Input p is a RationalPolynomial in (extension variables A_0..A_{k-1} of the
// prefix tower) + targetVar. "Substituting A_j = alpha_j" is reduction modulo
// m_j; if the substitution makes the polynomial vanish identically, the Lazard
// residual is recovered as the lowest derivative-order ∂^m/∂A_j^m that does NOT
// vanish (equivalent to dividing out (A_j-alpha_j)^m, up to the harmless m!
// factor — roots/sign unchanged). The result is a univariate in targetVar whose
// coefficients are reduced tower elements (in A_0..A_{k-1}).
//
// EXACT. Replaces ordinary specializeToUnivariate in the Lazard lift path;
// ordinary specialization is just the recorded multiplicity-0 case.
// ---------------------------------------------------------------------------

enum class ValuationStatus { Complete, AllDerivativesZero };

struct LazardValuationStep {
    VarId var;            // extension variable A_j processed
    int multiplicity;     // derivative order that recovered a nonzero residual
};

struct LazardValuationResult {
    ValuationStatus status = ValuationStatus::Complete;
    RationalPolynomial univariate;          // in targetVar + reduced tower coeffs
    std::vector<LazardValuationStep> trace; // [H3] replay witnesses
    bool complete() const { return status == ValuationStatus::Complete; }
};

// Evaluate p at the prefix tower; targetVar is the lift variable (not reduced).
LazardValuationResult lazardEvaluateToUnivariate(const RationalPolynomial& p,
                                                 VarId targetVar,
                                                 const TowerContext& ctx);

}  // namespace xolver
