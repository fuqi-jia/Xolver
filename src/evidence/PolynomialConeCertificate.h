#pragma once

#include "contracts/PolynomialProof.h"
#include "contracts/PolynomialDomain.h"
#include "base/WorkBudget.h"
#include <chrono>

namespace xolver {

struct PolynomialConePremise {
    PolynomialProof poly;
    Relation rel;
};

struct PolynomialConeStep {
    enum class Rule { One, Premise, IntegralGap, Square, Product, EqualityMultiple };
    Rule rule = Rule::One;
    size_t source = 0, left = 0, right = 0;
    // Square base or an equality multiplier; unused by other rules.
    PolynomialProof factor;
    mpq_class scale = 1; // positive normalization, independently checked
};

struct PolynomialConeCertificate {
    std::vector<PolynomialConeStep> steps;
    std::vector<mpq_class> weights;
};

struct PolynomialConeFact {
    PolynomialProof poly;
    bool equality = false, strict = false;
    std::vector<size_t> sources;
};

// Reconstruct one proof step from preceding facts. This is also used by the
// search producer so the proof rules and their domain conditions stay shared.
std::optional<PolynomialConeFact> derivePolynomialConeStep(
    const PolynomialConeStep&, const std::vector<PolynomialConePremise>&,
    const std::vector<PolynomialConeFact>& preceding, PolynomialDomain,
    WorkBudget&, std::chrono::steady_clock::time_point deadline);

// A valid certificate is an exact zero polynomial made from nonnegative
// weighted nonnegative facts and arbitrary weighted equalities. At least one
// positive contribution must be strict. Returns only original premise indices.
std::optional<std::vector<size_t>> checkPolynomialConeCertificate(
    const PolynomialConeCertificate&, const std::vector<PolynomialConePremise>&,
    PolynomialDomain, std::chrono::steady_clock::time_point deadline);

} // namespace xolver
