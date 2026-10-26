#include "algebra/interval/IntervalEvaluator.h"
#include "algebra/interval/IntervalOperations.h"
#include "base/WorkBudget.h"
#include <algorithm>
#include <cassert>

namespace xolver {

IntervalEvaluator::IntervalEvaluator(PolynomialKernel& kernel)
    : kernel_(kernel) {}

std::optional<IntervalZ> IntervalEvaluator::getVariableInterval(
    const std::string& var, const ReasonedBox& box) const {

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
        case Relation::Lt:
            return polyInterval.lo >= 0;
        case Relation::Gt:
            return polyInterval.hi <= 0;
        case Relation::Eq:
            return !polyInterval.containsZero();
        case Relation::Neq:
            return polyInterval.lo == 0 && polyInterval.hi == 0;
        default:
            return false;
    }
}

std::optional<ReasonedInterval> IntervalEvaluator::evaluateTerms(
    const std::vector<PolynomialKernel::MonomialTerm>& terms,
    const ReasonedBox& box, std::optional<VarId> omitted) const {
    WorkBudget budget;
    IntervalZ range{0, 0};
    std::vector<SatLit> reasons;
    try {
        for (const auto& term : terms) {
            if (omitted && std::any_of(term.powers.begin(), term.powers.end(),
                [&](const auto& power) { return power.first == *omitted; })) continue;
            budget.tick(mpz_sizeinbase(term.coefficient.get_mpz_t(), 2));
            IntervalZ product{term.coefficient, term.coefficient};
            for (const auto& [variable, exponent] : term.powers) {
                const auto bound = box.get(std::string(kernel_.varName(variable)));
                if (!bound || bound->interval.isEmpty() || exponent < 0)
                    return std::nullopt;
                const auto bits = std::max(mpz_sizeinbase(bound->interval.lo.get_mpz_t(), 2),
                                           mpz_sizeinbase(bound->interval.hi.get_mpz_t(), 2));
                if (exponent && bits > SIZE_MAX / static_cast<size_t>(exponent))
                    return std::nullopt;
                budget.tick(bits * static_cast<size_t>(exponent));
                product = intervalMul(product, intervalPow(bound->interval, exponent));
                reasons.insert(reasons.end(), bound->reasons.begin(), bound->reasons.end());
            }
            range = intervalAdd(range, product);
        }
    } catch (const ResourceExhausted&) {
        return std::nullopt;
    }
    std::sort(reasons.begin(), reasons.end(), [](SatLit a, SatLit b) {
        return a.var != b.var ? a.var < b.var : a.sign < b.sign;
    });
    reasons.erase(std::unique(reasons.begin(), reasons.end()), reasons.end());
    return ReasonedInterval{std::move(range), std::move(reasons)};
}

IntervalEvalResult IntervalEvaluator::run(
    const IntervalConstraint& constraint,
    const ReasonedBox& box) {

    auto vars = kernel_.variables(constraint.poly);
    if (vars.size() != 1) {
        // Evaluate each monomial over the complete reasoned box. Different
        // occurrences may be correlated, so products/sums deliberately keep
        // an over-approximation; only exclusion of zero proves a conflict.
        const auto terms = kernel_.terms(constraint.poly);
        if (!terms) return {IntervalEvalStatus::NoChange, {}};
        auto range = evaluateTerms(*terms, box);
        if (!range || !isDefinitelyViolated(range->interval, constraint.rel))
            return {IntervalEvalStatus::NoChange, {}};
        return {IntervalEvalStatus::DefinitelyViolated, std::move(range->reasons)};
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

} // namespace xolver
