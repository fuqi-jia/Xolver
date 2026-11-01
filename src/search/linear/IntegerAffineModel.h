#pragma once

#include "search/linear/IntegerReasoner.h"
#include <functional>

namespace xolver {

using IntegerPoint = std::unordered_map<std::string, mpq_class>;

using IntegerBoundsLookup = std::function<
    std::optional<std::pair<mpz_class, mpz_class>>(const std::string&)>;

// Under the supplied asserted integer bounds:
// dividend + offset = 2^exponent * (+/- quotient) + remainder,
// with 0 <= remainder < 2^exponent. The sign is negative iff
// negateQuotient is set. This describes a unique Euclidean decomposition,
// including negative dividends; it does not itself prove infeasibility.
struct IntegerRadixDecomposition {
    std::string dividend, quotient, remainder;
    mpz_class offset;
    unsigned exponent;
    bool negateQuotient;
    mpz_class remainderLower, remainderUpper;
};

std::optional<IntegerRadixDecomposition> findIntegerRadixDecomposition(
    const NormalizedConstraint& equation, const IntegerBoundsLookup& bounds);

// Construct an integer candidate on the affine lattice of the equalities.
// Coordinates absent from the equalities retain their seed values. For a
// lattice with at most one free coordinate, all remaining constraints are
// solved exactly as bounds/exclusions on that integer parameter. Otherwise
// no candidate is proposed; callers continue their ordinary search. A failure
// is never an UNSAT result. Constraints must be normalized over integers.
std::optional<IntegerPoint> findIntegerAffineModel(
    const std::vector<NormalizedConstraint>& constraints, const IntegerPoint& seed);

} // namespace xolver
