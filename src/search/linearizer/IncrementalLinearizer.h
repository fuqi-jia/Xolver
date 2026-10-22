#pragma once

#include "search/linearizer/LinearizationResult.h"
#include "search/linearizer/NonlinearTermAbstraction.h"
#include "search/linearizer/McCormickGenerator.h"
#include "search/linearizer/SquareCutGenerator.h"
#include "search/linearizer/LinearizationCache.h"
#include "algebra/linear/LinearConstraintNormalizer.h"
#include "search/coordination/TheoryAtomRegistry.h"
#include "search/coordination/TheoryLemmaDatabase.h"
#include <gmpxx.h>
#include <string>
#include <unordered_map>
#include <vector>

namespace xolver {

struct LinearizationConfig {
    size_t maxLemmas = 10;
    size_t maxCutsPerTerm = 4;
};

class BoundStore;

class IncrementalLinearizer {
public:
    explicit IncrementalLinearizer(PolynomialKernel& kernel,
                                   TheoryAtomRegistry* registry);

    LinearizationResult run(
        const std::vector<LinearizationConstraint>& constraints,
        const BoundStore& bounds,
        TheoryId owner,
        const LinearizationConfig& config = {},
        // Optional base-variable values used
        // as the square-tangent point so cuts refine around the current model.
        // null -> tangent at the bound midpoint (legacy behavior).
        const std::unordered_map<std::string, mpq_class>* modelPoints = nullptr);

    // Cache marking (called by adapter after successful enqueue)
    void markEmitted(const CutCacheKey& key);

    void clearCache() { cache_.clear(); }

private:
    PolynomialKernel& kernel_;
    TheoryAtomRegistry* registry_;
    NonlinearTermAbstraction abstraction_;
    McCormickGenerator mcGen_;
    SquareCutGenerator sqGen_;
    LinearizationCache cache_;

    TheoryLemma buildAbstractionLemma(SatLit nonlinearReason, SatLit linearizedLit);
    TheoryLemma buildCutLemma(SatLit nonlinearReason,
                               const std::vector<SatLit>& boundReasons,
                               SatLit cutLit);
};

} // namespace xolver
