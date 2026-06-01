#pragma once

// HybridPartitionStats — Task NRA-HYB Step 1 deliverable.
//
// Reports the linear / nonlinear partition pattern of the active NRA
// constraint set, plus the corresponding variable partition into
// pure-linear (V_L), pure-nonlinear (V_N) and mixed (V_M). This is the
// scaffolding data master's hybrid Simplex+CAC algorithm needs to
// decide whether the partition surface justifies a full coordinated
// solver.
//
// Step 1 (this file): partition + stats only. No solver wiring.
// Step 2+ (future): wire Simplex to V_L ∪ V_M, then CAC on V_N with
// V_M fixed; iterate until convergence or budget.
//
// Soundness: report-only. Never modifies solver state. Gated by
// XOLVER_NRA_HYB_PARTITION_STATS=1.

#include "theory/arith/poly/PolynomialKernel.h"
#include <vector>
#include <cstdint>

namespace xolver {

struct HybridPartitionReport {
    uint32_t totalConstraints = 0;
    uint32_t linearConstraints = 0;
    uint32_t nonlinearConstraints = 0;
    uint32_t totalVars = 0;
    uint32_t pureLinearVars = 0;     // V_L
    uint32_t pureNonlinearVars = 0;  // V_N
    uint32_t mixedVars = 0;          // V_M

    double linearConstraintFraction() const {
        return totalConstraints > 0
            ? static_cast<double>(linearConstraints) / totalConstraints
            : 0.0;
    }
    double mixedVarFraction() const {
        return totalVars > 0
            ? static_cast<double>(mixedVars) / totalVars
            : 0.0;
    }
};

// Walk the active PolyId list, classify each constraint as linear (every
// monomial degree ≤ 1) or nonlinear, build the variable partition,
// and return the report. Pure function of (polys, kernel) — no solver
// state mutation. Callers pass a PolyId list because each upstream
// solver type wraps PolyId differently (NraSolver::PresolveCstr,
// NraLocalSearch::Constraint, …); the shared PolyId surface is all
// the analysis needs.
HybridPartitionReport computePartition(
    const std::vector<PolyId>& polys,
    PolynomialKernel& kernel);

// Emit report to stderr in a single line under
// XOLVER_NRA_HYB_PARTITION_STATS=1. Idempotent (the caller decides
// when to dump — typically once per solve at first check entry).
void maybeDumpPartitionReport(const HybridPartitionReport& report);

} // namespace xolver
