#pragma once

#include "search/nia/NiaTypes.h"
#include "search/nia/preprocess/NiaNormalizer.h"
#include "search/nia/core/DomainStore.h"
#include "contracts/TheorySolver.h"

namespace xolver {

/**
 * LinearNiaDomainReasoner: extracts domain updates from single-variable
 * linear constraints of the form a*x + c rel 0.
 */
class LinearNiaDomainReasoner {
public:
    explicit LinearNiaDomainReasoner(PolynomialKernel& kernel);

    NiaReasoningResult run(const std::vector<NormalizedNiaConstraint>& constraints,
                           DomainStore& domains);

private:
    PolynomialKernel& kernel_;

    // Try to extract a*x + c from polynomial. Returns true if linear in single var.
    bool extractLinearForm(PolyId poly, mpz_class& a, mpz_class& c, std::string& var) const;
};

} // namespace xolver
