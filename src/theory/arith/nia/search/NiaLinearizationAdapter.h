#pragma once

#include "theory/arith/linearizer/IncrementalLinearizer.h"
#include "theory/arith/linearizer/LinearizationResult.h"
#include "theory/arith/nia/preprocess/NiaNormalizer.h"
#include "theory/arith/nia/core/DomainStore.h"
#include "theory/core/TheorySolver.h"
#include <vector>

namespace zolver {

// Generic active assignment for mirror step (matches NiaSolver::ActiveAssignment)
struct LinearizerActiveAssignment {
    int level;
    SatLit lit;
    TheoryAtomRecord atom;
    bool value;
};

class NiaLinearizationAdapter {
public:
    explicit NiaLinearizationAdapter(PolynomialKernel& kernel,
                                     TheoryAtomRegistry* registry);

    // Step A: mirror effective active linear bounds to LIA
    std::vector<TheoryLemma> mirrorActiveLinearBounds(
        const std::vector<LinearizerActiveAssignment>& activeAssignments,
        TheoryId targetLinearTheory);

    // Step B: run linearizer on nonlinear constraints
    LinearizationResult runLinearizer(
        const std::vector<NormalizedNiaConstraint>& nonlinearConstraints,
        const DomainStore& domains,
        TheoryLemmaStorage& lemmaDb,
        const LinearizationConfig& config = {});

    // Cache marking (called by NiaSolver after successful enqueue)
    void markEmitted(const CutCacheKey& key);

    void clearCache() { linearizer_.clearCache(); }

private:
    PolynomialKernel& kernel_;
    IncrementalLinearizer linearizer_;
    TheoryAtomRegistry* registry_;

    // Extract linear view from a PolynomialAtomPayload if the polynomial is degree ≤ 1.
    std::optional<std::pair<LinearFormKey, mpq_class>> tryExtractLinearForm(
        const PolynomialAtomPayload& payload);
};

} // namespace zolver
