#include "theory/arith/nia/IntervalEvaluator.h"
#include <algorithm>
#include <cassert>

namespace nlcolver {

IntervalEvaluator::IntervalEvaluator(PolynomialKernel& kernel)
    : kernel_(kernel) {}

std::optional<IntervalZ> IntervalEvaluator::getVariableInterval(
    const std::string& var, const DomainStore& domains) const {

    const IntDomain* d = domains.getDomain(var);
    if (!d || !d->hasLower || !d->hasUpper) return std::nullopt;
    return IntervalZ{d->lower.value, d->upper.value};
}

IntervalZ IntervalEvaluator::intervalAdd(const IntervalZ& a, const IntervalZ& b) {
    return {a.lo + b.lo, a.hi + b.hi};
}

IntervalZ IntervalEvaluator::intervalSub(const IntervalZ& a, const IntervalZ& b) {
    return {a.lo - b.hi, a.hi - b.lo};
}

IntervalZ IntervalEvaluator::intervalNeg(const IntervalZ& a) {
    return {-a.hi, -a.lo};
}

IntervalZ IntervalEvaluator::intervalMul(const IntervalZ& a, const IntervalZ& b) {
    mpz_class ac = a.lo * b.lo;
    mpz_class ad = a.lo * b.hi;
    mpz_class bc = a.hi * b.lo;
    mpz_class bd = a.hi * b.hi;
    mpz_class lo = std::min({ac, ad, bc, bd});
    mpz_class hi = std::max({ac, ad, bc, bd});
    return {lo, hi};
}

IntervalZ IntervalEvaluator::intervalPow(const IntervalZ& a, uint32_t k) {
    if (k == 0) return {mpz_class(1), mpz_class(1)};
    if (k == 1) return a;

    if (k % 2 == 0) {
        // Even power
        if (a.containsZero()) {
            // 0 in [lo, hi]: minimum is 0, maximum is max(lo^2, hi^2)
            mpz_class lo2 = a.lo * a.lo;
            mpz_class hi2 = a.hi * a.hi;
            return {mpz_class(0), std::max(lo2, hi2)};
        } else {
            // 0 not in [lo, hi]: minimum is min(lo^2, hi^2)
            mpz_class lo2 = a.lo * a.lo;
            mpz_class hi2 = a.hi * a.hi;
            return {std::min(lo2, hi2), std::max(lo2, hi2)};
        }
    } else {
        // Odd power: monotonic
        mpz_class loK = a.lo;
        mpz_class hiK = a.hi;
        for (uint32_t i = 1; i < k; ++i) {
            loK *= a.lo;
            hiK *= a.hi;
        }
        return {loK, hiK};
    }
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

NiaReasoningResult IntervalEvaluator::run(
    const std::vector<NormalizedNiaConstraint>& constraints,
    const DomainStore& domains) {

    for (const auto& c : constraints) {
        auto vars = kernel_.variables(c.poly);
        if (vars.size() != 1) continue; // Phase 3: only single-variable

        const std::string& var = vars[0];
        auto intervalOpt = getVariableInterval(var, domains);
        if (!intervalOpt) continue; // Need both bounds

        auto coeffsOpt = kernel_.getIntegerCoefficients(c.poly, var);
        if (!coeffsOpt) continue;

        IntervalZ polyInterval = evaluatePolynomial(*coeffsOpt, *intervalOpt);

        if (isDefinitelyViolated(polyInterval, c.rel)) {
            // Conflict: collect all active constraint reasons as coarse conflict
            std::vector<SatLit> conflictLits;
            for (const auto& ac : constraints) {
                conflictLits.push_back(ac.reason.negated());
            }
            return {NiaReasoningKind::Conflict,
                    TheoryConflict{conflictLits},
                    std::nullopt};
        }
    }

    return {NiaReasoningKind::NoChange, std::nullopt, std::nullopt};
}

} // namespace nlcolver
