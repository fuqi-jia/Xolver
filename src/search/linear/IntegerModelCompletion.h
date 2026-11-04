#pragma once

#include <chrono>
#include <cstddef>
#include <functional>
#include <optional>
#include <span>
#include <unordered_map>
#include <gmpxx.h>

namespace xolver {

class GeneralSimplex;

using SimplexIntegerPoint = std::unordered_map<int, mpq_class>;

struct IntegerCompletionStatistics {
    size_t nodes = 0, fractionalPoints = 0, pins = 0;
    bool exhausted = false;
};

// Search neighboring integer pins inside an existing affine relaxation. Only
// the supplied original columns require integrality; slack columns need not.
// Every pin is scoped and removed on return or cancellation. Bounds, caller
// levels and conflict explanations are preserved. The retained simplex point
// may require check() after an unsuccessful search.
//
// A point satisfies the affine context and is integral on every supplied
// column. Clients must still validate their complete original obligations.
// Missing a point, including exhaustion, never establishes infeasibility.
std::optional<SimplexIntegerPoint> completeIntegerModel(
    GeneralSimplex& simplex, std::span<const int> columns,
    std::chrono::steady_clock::time_point deadline, size_t nodeLimit,
    const std::function<void()>& tick,
    IntegerCompletionStatistics* statistics = nullptr);

} // namespace xolver
