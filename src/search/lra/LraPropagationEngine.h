#pragma once

#include "search/lra/DeltaRational.h"
#include "contracts/SatSolver.h"
#include "search/lra/GeneralSimplex.h"
#include <cstddef>
#include <vector>

namespace xolver {

// ---------------------------------------------------------------------------
// PropagationBudget: controls how much work propagateAll() does
// ---------------------------------------------------------------------------
struct PropagationBudget {
    int maxDerivedBounds = 512;
    int maxIterations = 2048;
    int maxReasonSize = 12;
    int maxTimeMs = 20;
};

// ---------------------------------------------------------------------------
// LraPropagationEngine: fixed-point bound propagation over tableau rows
//
// Derives explained bounds to a resource-bounded fixpoint in a local overlay.
// The simplex snapshot stays unchanged; explanations contain original SAT
// premises, including for bounds reached through several rows.
// ---------------------------------------------------------------------------
class LraPropagationEngine {
public:
    // -------------------------------------------------------------------------
    struct ExplainedBound {
        int var;
        bool isLower;
        DeltaRational value;
        std::vector<SatLit> reasons;
    };
    // -------------------------------------------------------------------------

    struct Statistics {
        std::size_t rowVisits = 0;
        std::size_t rowSnapshots = 0;
        std::size_t snapshotHits = 0;
        std::size_t termPairs = 0;
    };

    LraPropagationEngine() = default;

    /** Derive all implied bounds reachable within budget.
     *  Returns vector of newly-derived bounds (not yet asserted).
     */
    std::vector<ExplainedBound> propagateAll(
        const GeneralSimplex& gs,
        const PropagationBudget& budget = {512, 2048, 12, 20},
        Statistics* statistics = nullptr);

};

} // namespace xolver
