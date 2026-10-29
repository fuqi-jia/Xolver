#pragma once

#include "search/refute/SignDefinitenessRefuter.h"

namespace xolver {

struct PolynomialSignStatistics {
    size_t rounds = 0;
    size_t inferredFacts = 0;
    size_t substitutions = 0;
    size_t cancellations = 0;
    size_t divisions = 0;
    size_t eliminations = 0;
    size_t variableLookups = 0;
    size_t variableIndexHits = 0;
    size_t indexedVariables = 0;
    bool exhausted = false;
};

// Explained, bounded sign closure over Q-polynomials. All rules hold over the
// reals and therefore also over integers. Zero factors are retained unless
// nonzeroness has been proved. Failure leaves the caller's obligation open.
std::optional<std::vector<SatLit>> refuteByPolynomialSignClosure(
    const std::vector<SignRefuteConstraint>& constraints,
    PolynomialSignStatistics* statistics = nullptr);

} // namespace xolver
