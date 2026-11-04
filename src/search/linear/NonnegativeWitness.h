#pragma once

#include <chrono>
#include <cstddef>
#include <gmpxx.h>
#include <optional>
#include <span>
#include <utility>
#include <vector>

namespace xolver {

struct NonnegativeEquation {
    std::vector<std::pair<size_t, mpq_class>> coefficients;
    mpq_class rhs = 0;
};

// Propose a sparse nonnegative solution using numerical Phase I, then recover
// and verify every equation over exact rationals. A result is an exact witness;
// absence, including numerical infeasibility, makes no decision about the LP.
std::optional<std::vector<mpq_class>> findNonnegativeWitness(
    size_t variables, std::span<const NonnegativeEquation>,
    std::chrono::steady_clock::time_point deadline);

} // namespace xolver
