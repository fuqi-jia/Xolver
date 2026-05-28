#pragma once

#include "theory/arith/poly/RationalPolynomial.h"
#include "theory/arith/nra/valuation/TowerAlgebraicKernel.h"
#include "expr/types.h"

namespace xolver {

// GCD over the tower field K = Q(alpha_0,...) of two polynomials f, g viewed as
// UNIVARIATE in targetVar with tower-element coefficients (each f, g is a
// RationalPolynomial in the extension variables + targetVar). Returns the monic
// (over K) gcd, as a RationalPolynomial in extension vars + targetVar.
//
// Euclidean algorithm with coefficient arithmetic in K (TowerKernel); the
// leading-coefficient inverse uses the exact tower field inverse. ok == false
// iff a required inverse fails (a minimal poly turned out reducible — the
// irreducible-min-poly contract is broken) => caller treats as Unknown.
//
// Used by the exact root-membership oracle: G = towerPolyGcd(F, q) collects the
// K-factors common to F and beta's defining polynomial q.
struct TowerGcdResult {
    RationalPolynomial gcd;   // monic over K, in extension vars + targetVar
    bool ok = true;
};

TowerGcdResult towerPolyGcd(const RationalPolynomial& f, const RationalPolynomial& g,
                            VarId targetVar, const TowerKernel& K);

}  // namespace xolver
