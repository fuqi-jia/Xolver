#pragma once

#include "algebra/poly/RationalPolynomial.h"

namespace xolver {

// Exact mathematical identity of p relation 0, independent of pool handles.
// The first coefficient is one; relation is Eq, Lt or Leq.
struct PolynomialConstraintKey {
    RationalPolynomial polynomial;
    Relation relation;
    bool operator<(const PolynomialConstraintKey&) const;
};

struct CanonicalPolynomialConstraint {
    PolynomialConstraintKey key;
    // Original constraint = (negated ? !key : key).
    bool negated = false;
};

// Divide by the first nonzero coefficient, reverse inequalities when negative,
// and represent complementary comparisons by one key and opposite polarity.
// Zero polynomials have no key; their comparisons should be evaluated directly.
std::optional<CanonicalPolynomialConstraint>
canonicalPolynomialConstraint(RationalPolynomial polynomial, Relation relation);

} // namespace xolver
