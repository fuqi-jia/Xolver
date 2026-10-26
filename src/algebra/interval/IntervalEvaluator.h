#pragma once

#include "algebra/interval/IntervalTypes.h"
#include "algebra/interval/ReasonedBox.h"
#include "algebra/poly/PolynomialKernel.h"
#include "contracts/TheorySolver.h"
#include "ir/types.h"
#include <gmpxx.h>

namespace xolver {

/**
 * IntervalEvalStatus: result of evaluating one constraint against a ReasonedBox.
 */
enum class IntervalEvalStatus {
    NoChange,         // cannot determine violation
    DefinitelyViolated // the constraint is definitely violated in this box
};

/**
 * IntervalEvalResult: theory-agnostic interval evaluation result.
 *
 * The caller (NIA adapter) is responsible for constructing the TheoryConflict
 * from the violated constraint reason + used interval reasons.
 */
struct IntervalEvalResult {
    IntervalEvalStatus status;
    std::vector<SatLit> usedReasons; // bound reasons that contributed to the interval
};

/**
 * IntervalConstraint: a lightweight constraint representation for interval evaluation.
 * Theory-agnostic — used by NIA, NRA, etc.
 */
struct IntervalConstraint {
    PolyId poly;
    Relation rel;
    SatLit reason;
};

/**
 * IntervalEvaluator: sound over-approx interval evaluation for polynomial constraints.
 *
 * For a single normalized constraint p(x) rel 0:
 *   1. Evaluate powers, products and sums with exact outward integer bounds.
 *   2. Requires every variable to have both bounds in the ReasonedBox.
 *   3. Computes the over-approx interval of p(x) over the variable's domain.
 *   4. If the interval proves the constraint is definitely violated:
 *      returns DefinitelyViolated with the used bound reasons.
 */
class IntervalEvaluator {
public:
    explicit IntervalEvaluator(PolynomialKernel& kernel);

    // Evaluate a single constraint against the box.
    IntervalEvalResult run(const IntervalConstraint& constraint,
                           const ReasonedBox& box);

    // Shared monomial enclosure for forward evaluation and backward
    // contraction. When omitted is set, evaluate only monomials independent
    // of that coordinate; callers separately justify isolating its terms.
    std::optional<ReasonedInterval> evaluateTerms(
        const std::vector<PolynomialKernel::MonomialTerm>& terms,
        const ReasonedBox& box, std::optional<VarId> omitted = std::nullopt) const;

private:
    PolynomialKernel& kernel_;

    // Build interval for a variable from the ReasonedBox.
    std::optional<IntervalZ> getVariableInterval(const std::string& var,
                                                  const ReasonedBox& box) const;

    // Evaluate a single-variable polynomial at an interval.
    // coeffs: [leading, ..., constant] from getIntegerCoefficients.
    IntervalZ evaluatePolynomial(const std::vector<mpz_class>& coeffs,
                                  const IntervalZ& xInterval) const;

    // Check if constraint is definitely violated given the polynomial interval.
    static bool isDefinitelyViolated(const IntervalZ& polyInterval, Relation rel);
};

} // namespace xolver
