#pragma once

#include "theory/arith/poly/PolynomialKernel.h"
#include "theory/arith/nra/core/CdcacTypes.h"
#include "theory/arith/nra/core/CdcacConstraint.h"
#include "theory/core/TheorySolver.h"
#include <gmpxx.h>
#include <vector>
#include <optional>
#include <memory>

namespace nlcolver {

class CdcacCore;
class LibpolyBackend;
class CdcacCache;

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

    // V5: push/pop for Solver::push/pop API
    void push();
    void pop(uint32_t n);

    // V5: cache access
    void setCache(CdcacCache* cache) { cache_ = cache; }

    // Model extraction: returns the last SAT sample point
    std::optional<SamplePoint> getModel() const;

    // Format an algebraic root as (AlgebraicNumber (poly ...) (lower ...) (upper ...))
    std::string formatAlgebraicRoot(const AlgebraicRoot& root) const;

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

    struct ScopeSnapshot {
        size_t activeSize;
        size_t trailSize;
    };

    struct PendingConflict {
        int level;
        TheoryConflict conflict;
        std::optional<CoveringCertificate> certificate;  // V5: optional certificate
    };

    struct PendingUnknown {
        int level;
    };

    PolynomialKernel* kernel_;

    std::vector<ActiveConstraint> active_;
    std::vector<TrailEntry> trail_;
    std::vector<ScopeSnapshot> scopeStack_;  // V5: push/pop scope stack
    std::optional<PendingConflict> pendingConflict_;
    std::optional<PendingUnknown> pendingUnknown_;

    // P2a: CDCAC core + algebra backend
    std::unique_ptr<LibpolyBackend> algebra_;
    std::unique_ptr<CdcacCore> core_;

    // V5: cache
    CdcacCache* cache_ = nullptr;

    // Last SAT model from CDCAC core
    std::optional<SamplePoint> lastModel_;
};

} // namespace nlcolver
