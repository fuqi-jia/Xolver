#pragma once

#include "theory/arith/nia/NiaNormalizer.h"
#include "theory/arith/nia/DomainStore.h"
#include "theory/arith/nia/IntegerModelValidator.h"
#include "theory/TheorySolver.h"

namespace nlcolver {

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
                              TheoryLemmaDatabase& lemmaDb);

private:
    PolynomialKernel& kernel_;

    static const mpz_class ENUMERATION_THRESHOLD;

    BoundedSolveResult enumerate(const std::vector<NormalizedNiaConstraint>& constraints,
                                  const DomainStore& domains,
                                  const IntegerModelValidator& validator,
                                  const std::vector<std::string>& vars);
};

} // namespace nlcolver
