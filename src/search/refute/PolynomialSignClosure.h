#pragma once

#include "search/refute/SignDefinitenessRefuter.h"
#include "contracts/PolynomialDomain.h"

namespace xolver {

struct PolynomialSignStatistics {
    size_t sourceConstraints = 0;
    size_t inputFacts = 0;
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

// Explained, bounded sign closure over Q-polynomials. Variables are real unless
// declared integer in the supplied domain. Zero factors are retained unless
// nonzeroness has been proved. Failure leaves the caller's obligation open.
// Input capacity counts distinct canonical facts after merging source aliases.
// An optional output receives explained new/strengthened facts even when the
// bounded search is incomplete. It is cleared on every call and on conflict.
std::optional<std::vector<SatLit>> refuteByPolynomialSignClosure(
    const std::vector<SignRefuteConstraint>& constraints,
    PolynomialSignStatistics* statistics = nullptr,
    PolynomialDomain domain = {},
    std::vector<PolynomialConsequence>* consequences = nullptr);

} // namespace xolver
