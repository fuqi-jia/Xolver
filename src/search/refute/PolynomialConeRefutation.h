#pragma once

#include "search/refute/SignDefinitenessRefuter.h"
#include "evidence/PolynomialConeCertificate.h"

namespace xolver {

struct PolynomialConeStatistics {
    size_t generators = 0, coefficientRows = 0, searches = 0;
    size_t products = 0, squares = 0, equalityMultiples = 0;
    size_t certificateSteps = 0, premises = 0;
    bool exhausted = false, certified = false;
};

// Search for an exact contradiction among products of nonnegative premises,
// unconditional squares, and polynomial multiples of equalities. Integer
// strict gaps require explicit domain metadata. A feasible coefficient LP is
// only a candidate certificate: the independent algebraic replay must pass.
// No result (including an infeasible coefficient LP) establishes source SAT.
std::optional<std::vector<SatLit>> refuteByPolynomialCone(
    const std::vector<SignRefuteConstraint>&,
    std::chrono::steady_clock::time_point deadline,
    PolynomialDomain domain = {}, PolynomialConeStatistics* = nullptr,
    PolynomialConeCertificate* = nullptr);

} // namespace xolver
