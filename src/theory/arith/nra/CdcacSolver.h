#pragma once

#include "theory/arith/poly/PolynomialKernel.h"
#include "theory/arith/nra/CdcacTypes.h"
#include "theory/arith/nra/CdcacConstraint.h"
#include "theory/TheorySolver.h"
#include <gmpxx.h>
#include <vector>
#include <optional>
#include <memory>

namespace nlcolver {

class CdcacCore;
class LibpolyBackend;

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
    ~CdcacSolver();

    void assertConstraint(PolyId poly, Relation rel, SatLit reason, int level);
    void backtrack(int level);
    TheoryCheckResult check();
    TheoryCheckResult check(CdcacEffort effort, void* trail);
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

    // P2a: CDCAC core + algebra backend
    std::unique_ptr<LibpolyBackend> algebra_;
    std::unique_ptr<CdcacCore> core_;
};

} // namespace nlcolver
