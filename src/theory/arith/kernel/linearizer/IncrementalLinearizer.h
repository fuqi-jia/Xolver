#pragma once

#include "theory/arith/kernel/linearizer/LinearizationResult.h"
#include "theory/arith/kernel/linearizer/NonlinearTermAbstraction.h"
#include "theory/arith/kernel/linearizer/McCormickGenerator.h"
#include "theory/arith/kernel/linearizer/SquareCutGenerator.h"
#include "theory/arith/kernel/linearizer/PowerCutGenerator.h"
#include "theory/arith/kernel/linearizer/BernsteinPowerCutGenerator.h"
#include "theory/arith/kernel/linearizer/MonomialBoundGenerator.h"
#include "theory/arith/kernel/linearizer/LinearizationCache.h"
#include "theory/arith/kernel/linear/LinearConstraintNormalizer.h"
#include "theory/arith/logics/nia/preprocess/NiaNormalizer.h"
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
    PowerCutGenerator   pwGen_;   // Phase 1: x^N for N >= 3
    BernsteinPowerCutGenerator bpGen_; // Phase 1c: Bernstein convex-hull
    MonomialBoundGenerator mbGen_;// Phase 2: c · ∏ x_i^{e_i}, k >= 2 factors
    LinearizationCache cache_;

    TheoryLemma buildAbstractionLemma(SatLit nonlinearReason, SatLit linearizedLit);
    TheoryLemma buildCutLemma(SatLit nonlinearReason,
                               const std::vector<SatLit>& boundReasons,
                               SatLit cutLit);
};

} // namespace xolver
