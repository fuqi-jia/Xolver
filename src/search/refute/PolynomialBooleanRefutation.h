#pragma once

#include "ir/NativeTerms.h"
#include "search/boolean/TheoryRefutation.h"

namespace xolver {
struct PolynomialBooleanStatistics {
    BooleanRefutationResult boolean;
    size_t convertedAtoms = 0;
    size_t theoryCalls = 0;
    size_t largestContext = 0;
    size_t signExhaustions = 0;
    long long theoryMicroseconds = 0;
    bool exhausted = false;
};

// Whole-formula Boolean abstraction with explained polynomial conflicts. The
// sign calculus holds over reals and integers alike. Only UNSAT is concluded;
// an open real relaxation never establishes integer feasibility.
bool refutePolynomialBoolean(const NativeTerms&, const std::vector<ExprId>&,
    const BooleanRefutationLimits&, PolynomialBooleanStatistics* = nullptr);
} // namespace xolver
