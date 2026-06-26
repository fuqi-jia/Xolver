#pragma once

#include "theory/arith/logics/nia/NiaTypes.h"
#include "theory/arith/logics/nia/preprocess/NiaNormalizer.h"
#include "theory/arith/logics/nia/core/DomainStore.h"
#include "theory/core/TheorySolver.h"

namespace xolver {

/**
 * SquareBoundReasoner: handles univariate square constraints of the form
 * x^2 + c rel 0 (i.e. x^2 rel -c).
 *
 * Supported:
 *   x^2 + c <= 0  ->  x^2 <= -c  -> bounds [-floor(sqrt(-c)), floor(sqrt(-c))]
 *   x^2 + c =  0  ->  x^2 =  -c  -> finite set {r, -r} if -c = r^2, or UNSAT
 *   x^2 + c != 0  ->  x^2 != -c  -> exclusions {r, -r} if -c = r^2, or tautology
 *
 * Not supported (returns NoChange):
 *   x^2 + c >= 0  ->  disjunction, deferred to Phase 2
 *   multi-variable, degree != 2, leading coeff != 1, linear term != 0
 */
class SquareBoundReasoner {
public:
    explicit SquareBoundReasoner(PolynomialKernel& kernel);

    NiaReasoningResult run(const std::vector<NormalizedNiaConstraint>& constraints,
                           DomainStore& domains);

private:
    PolynomialKernel& kernel_;

    // Check if poly is of the form x^2 + c (single var, degree 2, leading coeff 1, no linear term).
    // On success, returns true and sets 'var' and 'constant' where poly = var^2 + constant.
    bool extractSquareForm(PolyId poly, std::string& var, mpz_class& constant) const;

    // Handle individual constraint.
    NiaReasoningResult handleConstraint(const NormalizedNiaConstraint& c, DomainStore& domains);
};

} // namespace xolver
