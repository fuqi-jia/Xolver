#pragma once

#include "theory/arith/nia/NiaTypes.h"
#include "theory/arith/nia/NiaNormalizer.h"
#include "theory/arith/nia/DomainStore.h"
#include "theory/TheorySolver.h"
#include <gmpxx.h>

namespace nlcolver {

/**
 * IntervalZ: integer interval [lo, hi] (inclusive).
 */
struct IntervalZ {
    mpz_class lo;
    mpz_class hi;

    bool isEmpty() const { return lo > hi; }
    bool contains(const mpz_class& v) const { return v >= lo && v <= hi; }
    bool containsZero() const { return lo <= 0 && hi >= 0; }
    mpz_class width() const { return hi - lo; }
};

/**
 * IntervalEvaluator: sound over-approx interval evaluation for single-variable
 * polynomial constraints.
 *
 * For each normalized constraint p(x) rel 0:
 *   1. Requires the variable to have both lower and upper bounds in DomainStore.
 *   2. Computes the over-approx interval of p(x) over the variable's domain.
 *   3. If the interval proves the constraint is definitely violated:
 *      returns Conflict with all active normalized constraint reasons.
 *
 * Multi-variable polynomials and unbounded variables are skipped (NoChange).
 */
class IntervalEvaluator {
public:
    explicit IntervalEvaluator(PolynomialKernel& kernel);

    NiaReasoningResult run(const std::vector<NormalizedNiaConstraint>& constraints,
                           const DomainStore& domains);

private:
    PolynomialKernel& kernel_;

    // Build interval for a variable from DomainStore.
    // Returns nullopt if the variable has no lower or no upper bound.
    std::optional<IntervalZ> getVariableInterval(const std::string& var,
                                                  const DomainStore& domains) const;

    // Evaluate a single-variable polynomial at an interval.
    // coeffs: [leading, ..., constant] from getIntegerCoefficients.
    IntervalZ evaluatePolynomial(const std::vector<mpz_class>& coeffs,
                                  const IntervalZ& xInterval) const;

    // Interval arithmetic primitives.
    static IntervalZ intervalAdd(const IntervalZ& a, const IntervalZ& b);
    static IntervalZ intervalSub(const IntervalZ& a, const IntervalZ& b);
    static IntervalZ intervalNeg(const IntervalZ& a);
    static IntervalZ intervalMul(const IntervalZ& a, const IntervalZ& b);
    static IntervalZ intervalPow(const IntervalZ& a, uint32_t k);

    // Check if constraint is definitely violated given the polynomial interval.
    static bool isDefinitelyViolated(const IntervalZ& polyInterval, Relation rel);
};

} // namespace nlcolver
