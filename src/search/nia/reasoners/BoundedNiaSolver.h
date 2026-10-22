#pragma once

#include "search/nia/preprocess/NiaNormalizer.h"
#include "search/nia/core/DomainStore.h"
#include "search/nia/search/IntegerModelValidator.h"
#include "contracts/TheorySolver.h"

namespace xolver {

enum class BoundedSolveStatus {
    Sat,              // exact model found and validated
    UnsatComplete,    // complete enumeration: no model exists
    UnknownBudget,    // budget exhausted
    UnknownUnsupported // interval evaluation unsupported
};

struct BoundedSolveResult {
    BoundedSolveStatus status;
    std::optional<IntegerModel> model;
    std::optional<TheoryConflict> conflict;
};

/**
 * BoundedNiaSolver: complete solver for finite-domain NIA.
 *
 * - Direct enumeration for small domains
 * - Interval branch-and-bound for larger domains (skeleton)
 */
class BoundedNiaSolver {
public:
    explicit BoundedNiaSolver(PolynomialKernel& kernel);

    BoundedSolveResult solve(const std::vector<NormalizedNiaConstraint>& constraints,
                              const DomainStore& domains,
                              const IntegerModelValidator& validator,
                              TheoryLemmaStorage& lemmaDb);

private:
    PolynomialKernel& kernel_;

    static mpz_class enumerationThreshold();

    BoundedSolveResult enumerate(const std::vector<NormalizedNiaConstraint>& constraints,
                                  const DomainStore& domains,
                                  const IntegerModelValidator& validator,
                                  const std::vector<std::string>& vars);
};

} // namespace xolver
