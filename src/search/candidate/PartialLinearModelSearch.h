#pragma once

#include "algebra/poly/PolynomialKernel.h"
#include <optional>
#include <cstddef>
#include <unordered_map>
#include <vector>

namespace xolver {

// Pin a monomial cover to boundary/simple candidates, solve the remaining
// linear problem, and validate every original polynomial at the complete point.
// Failure has no refutation meaning. No state or local conflict escapes a call.
class PartialLinearModelSearch {
public:
    struct Constraint { PolyId poly; Relation rel; };
    using Model = std::unordered_map<VarId, mpq_class>;
    struct Statistics {
        size_t variables = 0, parameters = 0, contexts = 0, linearChecks = 0;
        size_t retainedEqualityVariables = 0;
        size_t choices = 0, rejectedChoices = 0, definitions = 0, modelChecks = 0, maxDepth = 0;
        bool exhausted = false;
    };

    // Integer clients require an integral complete model; real clients accept
    // rational models. Endpoint ordering is shared; admissibility is domain
    // specific. This method never returns a conflict or an UNSAT result.
    static std::optional<Model> trySolve(const std::vector<Constraint>& constraints,
                                         PolynomialKernel& kernel,
                                         bool integerDomain = false,
                                         Statistics* statistics = nullptr);
};

} // namespace xolver
