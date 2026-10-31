#pragma once

#include "search/lra/DeltaRational.h"
#include "contracts/SatSolver.h"
#include "search/lra/GeneralSimplex.h"
#include <cstddef>
#include <functional>
#include <memory>
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
        std::size_t unproductiveSnapshots = 0;
        std::size_t retainedSnapshotHits = 0;
        std::size_t changedInputs = 0;
        std::size_t expiredSources = 0;
    };

    // Return false when the consumer has enough conclusions. Consumer time is
    // separate from the row arithmetic budget, as with post-scan processing.
    // The bound is already included in the result; references are valid during the
    // callback. Consumers must not mutate the simplex while it is scanned.
    using BoundConsumer = std::function<bool(const ExplainedBound&)>;

    LraPropagationEngine();
    ~LraPropagationEngine();
    LraPropagationEngine(const LraPropagationEngine&);
    LraPropagationEngine& operator=(const LraPropagationEngine&);
    LraPropagationEngine(LraPropagationEngine&&) noexcept;
    LraPropagationEngine& operator=(LraPropagationEngine&&) noexcept;

    /** Derive implied bounds until the budget or consumer stops the scan.
     *  Returns vector of newly-derived bounds (not yet asserted).
     */
    std::vector<ExplainedBound> propagateAll(
        const GeneralSimplex& gs,
        const PropagationBudget& budget = {512, 2048, 12, 20},
        Statistics* statistics = nullptr,
        const BoundConsumer& consume = {});

private:
    struct State;
    std::unique_ptr<State> state_;
    // A bounded check resumes the circular row/side scan so
    // that a large tableau's prefix cannot permanently starve its suffix.
    std::size_t nextSeed_ = 0;
};

} // namespace xolver
