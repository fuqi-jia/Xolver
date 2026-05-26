#pragma once

#include "expr/types.h"
#include "theory/arith/poly/RationalPolynomial.h"
#include <string>

namespace zolver {

class PolynomialKernel;

/**
 * PolynomialNormalizer: canonical string key for polynomial deduplication.
 *
 * V2-1 minimal: key is a deterministic string representation of the
 * normalized rational polynomial.  Future versions may use a hash-based
 * key for performance.
 */
class PolynomialNormalizer {
public:
    using CanonicalKey = std::string;

    explicit PolynomialNormalizer(PolynomialKernel& kernel);

    /** Canonical key for a PolyId. */
    CanonicalKey canonicalKey(PolyId p);

    /** Canonical key for a RationalPolynomial. */
    CanonicalKey canonicalKey(const RationalPolynomial& rp);

private:
    PolynomialKernel& kernel_;
};

} // namespace zolver
