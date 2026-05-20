#pragma once

#include "DeltaRational.h"
#include "sat/SatSolver.h"
#include "GeneralSimplex.h"
#include <gmpxx.h>
#include <vector>
#include <unordered_map>
#include <queue>
#include <chrono>

namespace nlcolver {

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
// Derives implied variable bounds from GeneralSimplex tableau rows without
// modifying solver state.  Operates on the current tableau / beta snapshot.
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

    LraPropagationEngine() = default;

    /** Derive all implied bounds reachable within budget.
     *  Returns vector of newly-derived bounds (not yet asserted).
     */
    std::vector<ExplainedBound> propagateAll(
        const GeneralSimplex& gs,
        const PropagationBudget& budget = {512, 2048, 12, 20});

private:
    // Work-queue entry
    struct WorkItem {
        int var;
        bool isLower;
    };

    // Key for deduplicating derived bounds
    struct DerivedBoundKey {
        int var;
        bool isLower;
        bool operator==(const DerivedBoundKey& o) const {
            return var == o.var && isLower == o.isLower;
        }
    };
    struct DerivedBoundKeyHash {
        size_t operator()(const DerivedBoundKey& k) const {
            return static_cast<size_t>(k.var) * 2 + (k.isLower ? 1 : 0);
        }
    };

    // State for one propagation run
    const GeneralSimplex* gs_ = nullptr;
    const PropagationBudget* budget_ = nullptr;
    std::vector<WorkItem> workQueue_;
    size_t workPos_ = 0;
    int iterationCount_ = 0;
    int derivedCount_ = 0;
    std::unordered_map<DerivedBoundKey, DeltaRational, DerivedBoundKeyHash> strongestDerived_;
    std::chrono::steady_clock::time_point startTime_;

    // Helpers
    void enqueue(int var, bool isLower);
    bool shouldStop() const;

    void computeRowLower(int basicVar);
    void computeRowUpper(int basicVar);

    bool tryDeriveBound(int var, bool isLower, const DeltaRational& value,
                        const std::vector<SatLit>& reasons);

    static std::vector<SatLit> collectReasons(
        const std::vector<std::pair<int, SatLit>>& reasons);

    static bool satLitLess(SatLit a, SatLit b) {
        if (a.var != b.var) return a.var < b.var;
        return a.sign < b.sign;
    }
    static bool satLitEqual(SatLit a, SatLit b) {
        return a.var == b.var && a.sign == b.sign;
    }
};

} // namespace nlcolver
