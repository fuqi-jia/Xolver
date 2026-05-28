#pragma once

#include "theory/arith/linearizer/LinearizationResult.h"
#include "theory/arith/linearizer/NonlinearTermAbstraction.h"
#include "theory/arith/linearizer/McCormickGenerator.h"
#include "theory/arith/linearizer/SquareCutGenerator.h"
#include "theory/arith/linearizer/LinearizationCache.h"
#include "theory/arith/linear/LinearConstraintNormalizer.h"
#include "theory/arith/nia/preprocess/NiaNormalizer.h"
#include "theory/core/TheoryAtomRegistry.h"
#include "theory/core/TheoryLemmaDatabase.h"
#include <gmpxx.h>
#include <string>
#include <unordered_map>
#include <vector>

namespace xolver {

struct LinearizationConfig {
    bool emitAllMcCormick = true;
    bool emitSquareSecant = true;
    bool emitSquareTangent = true;
    bool emitSquareNonneg = true;
    size_t maxLemmas = 10;
    size_t maxCutsPerTerm = 4;
};

class BoundStore;

class IncrementalLinearizer {
public:
    explicit IncrementalLinearizer(PolynomialKernel& kernel,
                                   TheoryAtomRegistry* registry);

    LinearizationResult run(
        const std::vector<NormalizedNiaConstraint>& constraints,
        const BoundStore& bounds,
        TheoryId owner,
        const LinearizationConfig& config = {},
        // XOLVER_NRA_LINEARIZE model-construction: optional base-var values used
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
