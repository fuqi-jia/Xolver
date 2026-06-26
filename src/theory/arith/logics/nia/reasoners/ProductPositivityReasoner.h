#pragma once

#include "theory/arith/logics/nia/NiaTypes.h"
#include "theory/arith/logics/nia/preprocess/NiaNormalizer.h"
#include "theory/arith/logics/nia/core/DomainStore.h"
#include "theory/arith/kernel/poly/PolynomialKernel.h"
#include <vector>

namespace xolver {

/**
 * ProductPositivityReasoner: bound-free integer product-positivity.
 *
 * Sound rule: for a constraint that is a single non-constant monomial plus a
 * constant, c*(v1*v2*...*vn) + d  REL  0, if it forces the monomial value
 * M = v1*...*vn >= L with L >= 1 and EVERY factor variable is known-nonneg,
 * then each factor vj >= 1 (if any vj = 0 the product is 0 < 1).
 *
 * This derives lower bounds (mutating the DomainStore) or, when a derived
 * lower bound empties a domain, a sound UNSAT conflict. It is the foundational
 * rule of the bound-free NIA refutation engine (357-class AProVE unsat).
 */
class ProductPositivityReasoner {
public:
    explicit ProductPositivityReasoner(PolynomialKernel& kernel);

    NiaReasoningResult run(const std::vector<NormalizedNiaConstraint>& constraints,
                           DomainStore& domains);

private:
    PolynomialKernel& kernel_;
};

} // namespace xolver
