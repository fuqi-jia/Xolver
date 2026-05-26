#pragma once

#include "theory/arith/poly/RationalPolynomial.h"
#include <vector>

namespace zolver {

/**
 * SubresultantEngine: subresultant polynomial remainder sequence (PRS).
 *
 * Computes the PRS of two primitive polynomials p, q w.r.t. variable var.
 * The last non-zero remainder is a GCD candidate.
 *
 * V2-4: used by GcdEngine for multivariate GCD extraction.
 */
class SubresultantEngine {
public:
    struct Remainder {
        RationalPolynomial poly;
        int degree = -1;
    };

    struct Result {
        std::vector<Remainder> sequence;
        RationalPolynomial gcdCandidate;
        bool hasParametricDegreeDrop = false;
    };

    /**
     * Compute subresultant PRS of p and q w.r.t. var.
     * Precondition: p and q are primitive w.r.t. var.
     */
    static Result run(const RationalPolynomial& p,
                      const RationalPolynomial& q,
                      VarId var);
};

} // namespace zolver
