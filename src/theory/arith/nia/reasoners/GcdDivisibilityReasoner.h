#pragma once

#include "theory/arith/nia/NiaTypes.h"
#include "theory/arith/nia/preprocess/NiaNormalizer.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include <vector>

namespace xolver {

/**
 * GcdDivisibilityReasoner: sound UNSAT refutation for NIA equalities by the
 * GCD-divisibility test.
 *
 * For an equality `Σ aᵢ·mᵢ + c₀ = 0` (the mᵢ are monomials over integer
 * variables, so each mᵢ is an integer), every term aᵢ·mᵢ is divisible by
 * g = gcd(|aᵢ|), hence the sum ≡ 0 (mod g). An integer solution therefore
 * requires g | c₀; if g ∤ c₀ the equality has no integer solution ⇒ UNSAT.
 *
 * This generalizes AlgebraicIntegerReasoner::checkGcdConflict (univariate only)
 * to arbitrary — including nonlinear — monomials by treating each distinct
 * monomial as a column via PolynomialKernel::terms(). It complements the
 * presolve Smith-NF pass by firing per-check, after substitution/branching.
 *
 * Soundness: all NIA variables are integers, so the divisibility argument is
 * exact. Only equalities are handled (inequalities carry slack). Pure-constant
 * equalities (no monomials, g = 0) are left to the trivial-constant stage.
 */
class GcdDivisibilityReasoner {
public:
    explicit GcdDivisibilityReasoner(PolynomialKernel& kernel);

    NiaReasoningResult run(const std::vector<NormalizedNiaConstraint>& constraints);

private:
    PolynomialKernel& kernel_;
};

} // namespace xolver
