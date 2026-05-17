#pragma once

#include "theory/arith/poly/RationalPolynomial.h"
#include "theory/arith/nra/CdcacTypes.h"

namespace nlcolver {

/**
 * GcdEngine: compute GCD candidate of two multivariate polynomials
 * using subresultant PRS, with mandatory exactDivide verification.
 *
 * V2-4: used by DegeneracyResolver for zero-resultant resolution.
 */
class GcdEngine {
public:
    struct Result {
        RationalPolynomial gcd;
        RationalPolynomial pQuot;  // p / gcd (if exact)
        RationalPolynomial qQuot;  // q / gcd (if exact)
        bool exact = false;
        bool hasParametricDegreeDrop = false;
        CdcacUnknownReason reason = CdcacUnknownReason::None;
    };

    /**
     * Compute GCD candidate of p and q w.r.t. variable var.
     *
     * Algorithm:
     * 1. Primitive part w.r.t. var.
     * 2. Subresultant PRS.
     * 3. Extract candidate g.
     * 4. Mandatory exactDivide verification: p == g * pQuot && q == g * qQuot.
     * 5. Parametric degree drop → hasParametricDegreeDrop = true.
     *
     * Hard rule: GCD candidate that fails exactDivide verification must NOT be used.
     */
    static Result gcdCandidateBySubresultant(
        const RationalPolynomial& p,
        const RationalPolynomial& q,
        VarId var);
};

} // namespace nlcolver
