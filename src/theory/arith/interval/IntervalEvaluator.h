#pragma once

#include "theory/arith/interval/IntervalTypes.h"
#include "theory/arith/interval/ReasonedBoxZ.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include "theory/core/TheorySolver.h"
#include "expr/types.h"
#include <gmpxx.h>

namespace nlcolver {

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
 *   1. If the polynomial is multi-variable → NoChange (single-var only for now).
 *   2. Requires the variable to have both lower and upper bounds in the ReasonedBoxZ.
 *   3. Computes the over-approx interval of p(x) over the variable's domain.
 *   4. If the interval proves the constraint is definitely violated:
 *      returns DefinitelyViolated with the used bound reasons.
 */
class IntervalEvaluator {
public:
    explicit IntervalEvaluator(PolynomialKernel& kernel);

    // Evaluate a single constraint against the box.
    IntervalEvalResult run(const IntervalConstraint& constraint,
                           const ReasonedBoxZ& box);

private:
    PolynomialKernel& kernel_;

    // Build interval for a variable from the ReasonedBox.
    std::optional<IntervalZ> getVariableInterval(const std::string& var,
                                                  const ReasonedBoxZ& box) const;

    // Evaluate a single-variable polynomial at an interval.
    // coeffs: [leading, ..., constant] from getIntegerCoefficients.
    IntervalZ evaluatePolynomial(const std::vector<mpz_class>& coeffs,
                                  const IntervalZ& xInterval) const;

    // Check if constraint is definitely violated given the polynomial interval.
    static bool isDefinitelyViolated(const IntervalZ& polyInterval, Relation rel);
};

} // namespace nlcolver
