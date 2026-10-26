#pragma once

#include "base/WorkBudget.h"
#include <gmpxx.h>
#include <optional>
#include <vector>

namespace xolver {

// An integer-valued form with finite, inclusive integer bounds. Coordinates
// refer to the same integer variables in every form supplied to an operation.
struct BoundedIntegerForm {
    std::vector<mpz_class> coefficients;
    mpz_class lower;
    mpz_class upper;
};

// For z = leftMultiplier*A + rightMultiplier*B, every value of z is divisible
// by divisor, but [lower, upper] contains no such value. A zero divisor means
// z is identically zero and the interval excludes zero.
struct IntegerIntervalConflict {
    mpz_class leftMultiplier;
    mpz_class rightMultiplier;
    mpz_class divisor;
    mpz_class lower;
    mpz_class upper;
};

// Search exact integer combinations using continued-fraction directions from
// pairs of coordinates. This is a sound cut-discovery rule; failure to find a
// certificate says nothing about feasibility. Throws ResourceExhausted when
// the caller's work or wall-clock budget is exhausted.
std::optional<IntegerIntervalConflict> findIntegerIntervalConflict(
    const BoundedIntegerForm& left, const BoundedIntegerForm& right,
    WorkBudget& budget);

// Independently recompute the combination, its interval and divisibility gap.
bool verifyIntegerIntervalConflict(const BoundedIntegerForm& left,
                                  const BoundedIntegerForm& right,
                                  const IntegerIntervalConflict& certificate);

} // namespace xolver
