#pragma once

#include "theory/arith/nia/core/NiaNormalizer.h"
#include "theory/arith/nia/search/IntegerModelValidator.h"
#include "theory/arith/nia/core/DomainStore.h"
#include <optional>

namespace nlcolver {

/**
 * NiaLocalSearch: heuristic SAT finder for NIA.
 *
 * Phase NIA-Core: skeleton only. Tries a few candidate assignments.
 */
class NiaLocalSearch {
public:
    explicit NiaLocalSearch(PolynomialKernel& kernel);

    std::optional<IntegerModel> tryFindModel(
        const std::vector<NormalizedNiaConstraint>& constraints,
        const DomainStore& domains);

private:
    PolynomialKernel& kernel_;

    mpz_class violation(const IntegerModel& model,
                        const std::vector<NormalizedNiaConstraint>& constraints) const;
};

} // namespace nlcolver
