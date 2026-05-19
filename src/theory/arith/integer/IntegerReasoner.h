#pragma once

#include "theory/arith/linear/LinearExpr.h"
#include "theory/core/TheorySolver.h"
#include "theory/arith/linear/LinearModelValidator.h"
#include "theory/core/TheoryAtomRegistry.h"
#include <gmpxx.h>
#include <vector>
#include <optional>

namespace nlcolver {

/**
 * NormalizedConstraint: integer-coefficient constraint in standard form.
 */
struct NormalizedConstraint {
    LinearFormKey lhs;   // integer coefficients
    mpq_class rhs;       // integer
    Relation rel;        // Eq, Leq, or Geq
};

/**
 * IntegerReasoner: cheap integer reasoning rules.
 *
 * All methods operate on normalized effective active constraints.
 */
class IntegerReasoner {
public:
    void setRegistry(TheoryAtomRegistry* r) { registry_ = r; }

    /**
     * Run all cheap integer reasoning rules on active atoms.
     *
     * Returns:
     *   - Conflict if GCD equality conflict detected
     *   - Lemma if inequality tightening or bound tightening detected
     *   - nullopt if no cheap reasoning applies
     */
    std::optional<TheoryCheckResult> run(
        const std::vector<ActiveLinearAtom>& activeAtoms);

    /**
     * Normalize an active constraint for integer reasoning.
     *
     * Steps:
     * 1. If value=false, negate relation.
     * 2. Convert strict LIA to non-strict.
     * 3. Convert >= to <= (multiply by -1).
     * 4. Clear denominators.
     * 5. Normalize sign (leading coefficient positive for single-var).
     */
    static std::optional<NormalizedConstraint> normalize(
        const LinearFormKey& lhs, const mpq_class& rhs,
        Relation rel, bool value);

    /**
     * Check GCD equality conflict.
     *
     * If g = gcd(|a_i|) and g ∤ c, the equality is unsatisfiable.
     */
    std::optional<TheoryConflict> checkGcdEqualityConflict(
        const NormalizedConstraint& c, SatLit lit);

    /**
     * Check GCD inequality tightening.
     *
     * If g = gcd(|a_i|), tighten a·x <= c to a·x <= g * floor(c/g).
     */
    std::optional<TheoryLemma> checkGcdInequalityTightening(
        const NormalizedConstraint& c, SatLit lit);

    /**
     * Single-variable integer bound tightening.
     *
     * e.g. 2x <= 11  =>  x <= 5
     */
    std::optional<TheoryLemma> singleVarBoundTighten(
        const NormalizedConstraint& c, SatLit lit);

    /**
     * Equality normalization by GCD.
     *
     * e.g. 6x + 10y = 8  =>  3x + 5y = 4
     */
    std::optional<TheoryLemma> normalizeEquality(
        const NormalizedConstraint& c, SatLit lit);

private:
    TheoryAtomRegistry* registry_ = nullptr;

    static mpz_class gcdAbs(const std::vector<std::pair<std::string, mpq_class>>& terms);
    static void clearDenominators(LinearFormKey& lhs, mpq_class& rhs);
};

} // namespace nlcolver
