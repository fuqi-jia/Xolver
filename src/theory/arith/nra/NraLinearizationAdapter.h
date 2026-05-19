#pragma once

#include "theory/arith/linearizer/IncrementalLinearizer.h"
#include "theory/arith/linearizer/LinearizationResult.h"
#include "theory/arith/linear/LinearConstraintNormalizer.h"
#include "theory/core/TheorySolver.h"
#include <vector>

namespace nlcolver {

// Generic active assignment for mirror step
struct GenericActiveAssignment {
    SatLit lit;
    TheoryAtomRecord atom;
    bool value;
};

class NraLinearizationAdapter {
public:
    explicit NraLinearizationAdapter(PolynomialKernel& kernel,
                                     TheoryAtomRegistry* registry);

    std::vector<TheoryLemma> mirrorActiveLinearBounds(
        const std::vector<GenericActiveAssignment>& activeAssignments,
        TheoryId targetLinearTheory);

    LinearizationResult runLinearizer(
        const std::vector<NormalizedNiaConstraint>& nonlinearConstraints,
        TheoryLemmaDatabase& lemmaDb);

    void markEmitted(const CutCacheKey& key);

private:
    PolynomialKernel& kernel_;
    IncrementalLinearizer linearizer_;
    TheoryAtomRegistry* registry_;
};

} // namespace nlcolver
