#pragma once

#include "theory/arith/nra/core/CdcacTypes.h"

namespace zolver {

class LibpolyBackend;

/**
 * SquarefreeEngine: compute the squarefree part of a univariate polynomial.
 *
 * Algorithm: f / gcd(f, f')
 *
 * V2-2: used in isolateRealRoots to ensure defining polynomials are squarefree.
 */
class SquarefreeEngine {
public:
    explicit SquarefreeEngine(LibpolyBackend& backend);

    struct Result {
        UniPolyId squarefree = NullUniPolyId;
        bool ok() const { return squarefree != NullUniPolyId; }
    };

    /**
     * Compute the squarefree part of f.
     * Returns NullUniPolyId if the computation fails.
     */
    Result compute(UniPolyId f);

private:
    LibpolyBackend& backend_;
};

} // namespace zolver
