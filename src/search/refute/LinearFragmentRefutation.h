#pragma once

#include "search/refute/SignDefinitenessRefuter.h"
#include <chrono>

namespace xolver {

struct LinearFragmentStatistics {
    size_t constraints = 0;
    size_t variables = 0;
    bool exhausted = false;
};

// Refute the linear subset of an arithmetic assignment over the reals. This
// relaxation is also sound for integer clients. Nonlinear constraints and
// disequalities are omitted; a feasible relaxation establishes no SAT result.
// Returned literals are the original premises of an exact Simplex conflict.
std::optional<std::vector<SatLit>> refuteLinearFragment(
    const std::vector<SignRefuteConstraint>&,
    std::chrono::steady_clock::time_point deadline,
    LinearFragmentStatistics* = nullptr);

} // namespace xolver
