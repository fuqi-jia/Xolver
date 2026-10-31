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
    size_t residueCalls = 0;
    size_t residueAssignments = 0;
    size_t residueExhaustions = 0;
    size_t linearCalls = 0;
    size_t linearConstraints = 0;
    size_t linearExhaustions = 0;
    long long linearMicroseconds = 0;
    long long theoryMicroseconds = 0;
    bool exhausted = false;
};

// Whole-formula Boolean abstraction with explained polynomial conflicts. The
// sign calculus holds over reals and integers alike. Modular conflicts use
// only atoms whose polynomial variables are explicitly integer-sorted.
// Only UNSAT is concluded; an open relaxation never establishes feasibility.
bool refutePolynomialBoolean(const NativeTerms&, const std::vector<ExprId>&,
    const BooleanRefutationLimits&, PolynomialBooleanStatistics* = nullptr);
} // namespace xolver
