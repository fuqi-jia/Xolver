#include "theory/arith/interval/IntervalEvaluator.h"
#include "theory/arith/interval/IntervalOperations.h"
#include <algorithm>
#include <cassert>

namespace zolver {

IntervalEvaluator::IntervalEvaluator(PolynomialKernel& kernel)
    : kernel_(kernel) {}

std::optional<IntervalZ> IntervalEvaluator::getVariableInterval(
    const std::string& var, const ReasonedBoxZ& box) const {

    auto riOpt = box.get(var);
    if (!riOpt) return std::nullopt;
    return riOpt->interval;
}

IntervalZ IntervalEvaluator::evaluatePolynomial(
    const std::vector<mpz_class>& coeffs, const IntervalZ& xInterval) const {

    // coeffs: [a_n, a_{n-1}, ..., a_0] for a_n*x^n + ... + a_1*x + a_0
    IntervalZ result{mpz_class(0), mpz_class(0)};

    for (size_t i = 0; i < coeffs.size(); ++i) {
        const mpz_class& coeff = coeffs[i];
        if (coeff == 0) continue;

        // power = degree - i
        size_t power = coeffs.size() - 1 - i;
        IntervalZ termInterval = intervalPow(xInterval, static_cast<uint32_t>(power));

        if (coeff != 1) {
            IntervalZ coeffInterval{coeff, coeff};
            termInterval = intervalMul(coeffInterval, termInterval);
        }

        result = intervalAdd(result, termInterval);
    }

    return result;
}

bool IntervalEvaluator::isDefinitelyViolated(const IntervalZ& polyInterval, Relation rel) {
    switch (rel) {
        case Relation::Leq:
            return polyInterval.lo > 0;
        case Relation::Geq:
            return polyInterval.hi < 0;
        case Relation::Eq:
            return !polyInterval.containsZero();
        case Relation::Neq:
            return polyInterval.lo == 0 && polyInterval.hi == 0;
        default:
            return false;
    }
}

IntervalEvalResult IntervalEvaluator::run(
    const IntervalConstraint& constraint,
    const ReasonedBoxZ& box) {

    auto vars = kernel_.variables(constraint.poly);
    if (vars.size() != 1) {
        // Single-variable only for now
        return {IntervalEvalStatus::NoChange, {}};
    }

    const std::string& var = vars[0];
    auto intervalOpt = getVariableInterval(var, box);
    if (!intervalOpt) {
        // Need both bounds
        return {IntervalEvalStatus::NoChange, {}};
    }

    auto coeffsOpt = kernel_.getIntegerCoefficients(constraint.poly, var);
    if (!coeffsOpt) {
        return {IntervalEvalStatus::NoChange, {}};
    }

    IntervalZ polyInterval = evaluatePolynomial(*coeffsOpt, *intervalOpt);

    if (isDefinitelyViolated(polyInterval, constraint.rel)) {
        // Collect used reasons from the variable's interval
        auto riOpt = box.get(var);
        std::vector<SatLit> usedReasons;
        if (riOpt) {
            usedReasons = riOpt->reasons;
        }
        return {IntervalEvalStatus::DefinitelyViolated, usedReasons};
    }

    return {IntervalEvalStatus::NoChange, {}};
}

} // namespace zolver
