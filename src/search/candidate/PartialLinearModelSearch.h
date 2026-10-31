#pragma once

#include "algebra/poly/PolynomialKernel.h"
#include <optional>
#include <cstddef>
#include <chrono>
#include <unordered_map>
#include <vector>

namespace xolver {

// Pin a small monomial cover, propagate explained rational fixed values into
// the remaining polynomial constraints, and complete the resulting linear
// problem. Candidate domains are immutable during each explained traversal;
// newly observed LP points refine a fresh traversal. Every original polynomial
// is checked at the complete point.
// Alternative covers share one call allocation and own independent contexts.
// A root refutation uses only original affine atoms and exact fixed values
// entailed by them. Sampled-parameter conflicts remain local to the traversal.
class PartialLinearModelSearch {
public:
    struct Constraint { PolyId poly; Relation rel; };
    using Model = std::unordered_map<VarId, mpq_class>;
    struct RootRefutation {
        // Indices into the supplied original constraints. Their conjunction
        // is infeasible over the reals, independently of candidate choices.
        std::vector<size_t> premises;
    };
    struct Allocation {
        std::chrono::milliseconds time;
        size_t work;
        explicit Allocation(std::chrono::milliseconds time = std::chrono::milliseconds(1000),
                            size_t work = 1000000) : time(time), work(work) {}
    };
    struct Statistics {
        // Parameter counts describe the last partition; work counters and
        // maximum depth include all partitions in the shared allocation.
        size_t variables = 0, parameters = 0, contexts = 0, linearChecks = 0;
        size_t retainedEqualityVariables = 0;
        size_t choices = 0, rejectedChoices = 0, definitions = 0, modelChecks = 0, maxDepth = 0;
        size_t backjumps = 0, skippedLevels = 0, explanationFallbacks = 0;
        size_t propagatedFacts = 0, propagationRounds = 0, maxActiveAtoms = 0, refinements = 0;
        bool exhausted = false;
    };

    // Integer clients require an integral complete model; real clients accept
    // rational models. Endpoint ordering is shared; admissibility is domain
    // specific. A missing model is inconclusive unless rootRefutation is set.
    // The optional refutation output is cleared on entry; exhaustion, rejected
    // candidates and unsupported arithmetic never produce a refutation.
    static std::optional<Model> trySolve(const std::vector<Constraint>& constraints,
                                         PolynomialKernel& kernel,
                                         bool integerDomain = false,
                                         Statistics* statistics = nullptr,
                                         Allocation allocation = Allocation(),
                                         std::optional<RootRefutation>* rootRefutation = nullptr);
};

} // namespace xolver
