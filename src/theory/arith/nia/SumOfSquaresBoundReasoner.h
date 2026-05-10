#pragma once

#include "theory/arith/nia/NiaTypes.h"
#include "theory/arith/nia/NiaNormalizer.h"
#include "theory/arith/nia/DomainStore.h"
#include "theory/TheorySolver.h"

namespace nlcolver {

/**
 * SumOfSquaresBoundReasoner: derives finite bounds from sum-of-squares constraints.
 *
 * Recognizes normalized polynomials of the form:
 *   x1^2 + x2^2 + ... + xn^2 + c  rel  0
 *
 * Where each squared term has coefficient +1, no cross terms, no linear terms.
 *
 * Supported:
 *   Σ xi^2 + c <= 0  =>  Σ xi^2 <= -c  =>  each xi ∈ [-floorSqrt(-c), floorSqrt(-c)]
 *   Σ xi^2 + c =  0  =>  Σ xi^2 =  -c  =>  same bounds (equality implies <=)
 *
 * If -c < 0 (i.e. c > 0), returns UNSAT since sum of squares is always >= 0.
 *
 * Not supported (NoChange):
 *   >=, !=, non-sum-of-squares polynomials.
 */
class SumOfSquaresBoundReasoner {
public:
    explicit SumOfSquaresBoundReasoner(PolynomialKernel& kernel);

    NiaReasoningResult run(const std::vector<NormalizedNiaConstraint>& constraints,
                           DomainStore& domains);

private:
    PolynomialKernel& kernel_;

    // Try to match poly as sum of pure squares with coefficient +1 each.
    // On success, returns true and fills 'vars' and 'constant' where
    // poly = Σ xi^2 + constant.
    bool extractSumOfSquaresForm(PolyId poly,
                                 std::vector<std::string>& vars,
                                 mpz_class& constant) const;

    NiaReasoningResult handleConstraint(const NormalizedNiaConstraint& c, DomainStore& domains);
};

} // namespace nlcolver
