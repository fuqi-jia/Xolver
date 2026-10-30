#pragma once

#include "search/refute/SignDefinitenessRefuter.h"
#include <chrono>

namespace xolver {

struct PolynomialLinearStatistics {
    size_t constraints = 0;
    size_t variables = 0;
    bool exhausted = false;
};

// Refute a polynomial assignment by an exact linear relaxation over the reals.
// Each distinct canonical monomial is an unconstrained shared column. This is
// also sound for integer clients; no integrality or product identities are
// assumed. Disequalities are omitted. Feasibility establishes no SAT result.
// Returned literals are the original premises of an exact Simplex conflict.
std::optional<std::vector<SatLit>> refutePolynomialLinearRelaxation(
    const std::vector<SignRefuteConstraint>&,
    std::chrono::steady_clock::time_point deadline,
    PolynomialLinearStatistics* = nullptr);

} // namespace xolver
