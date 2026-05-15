#pragma once

#include "theory/arith/poly/PolynomialKernel.h"
#include "theory/arith/nra/CdcacTypes.h"
#include "theory/TheorySolver.h"
#include <gmpxx.h>
#include <vector>
#include <optional>

namespace nlcolver {

/**
 * CDCAC (Conflict-Driven Cylindrical Algebraic Covering) engine.
 *
 * Core NRA solver responsible for polynomial constraint management
 * and checking. Does NOT inherit TheorySolver; it is driven by
 * NraSolver (the facade).
 */
class CdcacSolver {
public:
    explicit CdcacSolver(PolynomialKernel* kernel);

    void assertConstraint(PolyId poly, Relation rel, SatLit reason, int level);
    void backtrack(int level);
    TheoryCheckResult check();
    TheoryCheckResult check(TheoryEffort effort, void* trail);
    void reset();

private:
    struct ActiveConstraint {
        PolyId poly;
        Relation rel;   // effective relation
        SatLit reason;  // assigned SAT literal
    };

    struct TrailEntry {
        int level;
        size_t activeSizeBefore;
    };

    struct PendingConflict {
        int level;
        TheoryConflict conflict;
    };

    struct PendingUnknown {
        int level;
    };

    PolynomialKernel* kernel_;

    std::vector<ActiveConstraint> active_;
    std::vector<TrailEntry> trail_;
    std::optional<PendingConflict> pendingConflict_;
    std::optional<PendingUnknown> pendingUnknown_;
};

} // namespace nlcolver
