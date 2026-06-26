#pragma once

#include "theory/arith/kernel/poly/PolynomialKernel.h"
#include "theory/arith/logics/nra/core/CdcacTypes.h"
#include "theory/arith/logics/nra/core/CdcacConstraint.h"
#include "theory/core/TheorySolver.h"
#include "util/RealValue.h"
#include <gmpxx.h>
#include <vector>
#include <optional>
#include <memory>

namespace xolver {

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
    // Step 2.1: cheap GLOBAL box-consistency refutation over the active constraints.
    // True ⇒ real-infeasible over all of ℝⁿ ⇒ UNSAT; fills reasonsOut with a sound
    // (superset) conflict. Meant to run as an EARLY pipeline stage, before the covering.
    bool globalBoxRefute(std::vector<SatLit>& reasonsOut);
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

    // Convert a CDCAC sample value (rational or algebraic root) to the unified
    // RealValue type — the bridge from the CDCAC number system to the rest of
    // the solver / model output.  Rational → RealValue::fromMpq; AlgebraicRoot
    // → RealValue::fromAlgebraic (defining-poly coefficients + isolation
    // interval pulled from the libpoly backend).
    RealValue sampleValueToRealValue(const RealAlg& v) const;

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

    bool simplexVarOrder_ = false;   // XOLVER_NRA_VARORDER_SIMPLEX

    // Last SAT model from CDCAC core
    std::optional<SamplePoint> lastModel_;
};

} // namespace xolver
