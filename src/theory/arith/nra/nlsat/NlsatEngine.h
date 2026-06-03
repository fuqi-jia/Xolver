#pragma once

// NlsatEngine — NRA backend for the MCSAT framework.
//
// "NLSAT" follows the historical name: a non-linear arithmetic engine that
// shares its trail with the SAT solver, picks real values for variables
// from currently-feasible cells, and explains conflicts via single-cell
// projection. The MCSAT framework (src/experimental/mcsat/) owns the
// trail; this class owns the algebra.
//
// Reuses the existing CDCAC infrastructure:
//   - AlgebraBackend (poly signAt, root isolation, projection)
//   - SingleCellProjection (for the explain function)
//   - LibPolyKernel (exact algebraic numbers)
//
// Soundness:
//   - validateModel uses ExactValidator / IntegerModelValidator style
//     evaluation — every assigned variable's value is substituted into
//     every asserted polynomial atom, and the relation tested with
//     exact arithmetic; Sat is reported only when all atoms hold.
//   - explainConflict produces a clause over original SAT literals
//     (the asserted atoms whose joint truth made the variable infeasible).
//     Currently the explanation is the simplest theory-valid form:
//     ¬lit1 ∨ ¬lit2 ∨ ... where the {lit_i} are exactly the asserted SAT
//     literals attached to the blocking atoms. A future refinement adds
//     cell-projection-derived bound disjuncts (the NLSAT "explanation
//     function" proper) — strictly stronger but not soundness-critical.
//   - When the engine cannot decide (libpoly unsupported case, etc.) it
//     returns ValueChoice{ok=false, blockingAtoms={}} which the framework
//     turns into an Unknown verdict, never UNSAT.

#include "experimental/mcsat/MCSatEngine.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include <memory>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace xolver {

class AlgebraBackend;
class CdcacCore;

namespace nlsat {

// Internal record for one asserted polynomial atom.
struct AssertedAtom {
    TheoryAtomRecord atom;
    bool value = true;
    int level = 0;
    SatLit assertedLit{};
};

class NlsatEngine : public mcsat::MCSatEngine {
public:
    NlsatEngine();
    ~NlsatEngine() override;

    // Inject the algebra backend (libpoly-backed) at construction time.
    // The framework guarantees the backend outlives the engine.
    void setAlgebra(PolynomialKernel* kernel, AlgebraBackend* backend);
    void setCoreIr(const class CoreIr* coreIr) { coreIr_ = coreIr; }

    // MCSatEngine API
    void reset() override;
    void onAssertAtom(const TheoryAtomRecord& atom, bool value, int level,
                      SatLit assertedLit) override;
    void onBacktrack(int targetLevel) override;
    VarId pickNextVar(const mcsat::MCSatTrail& trail) override;
    mcsat::ValueChoice pickValue(VarId var,
                                 const mcsat::MCSatTrail& trail) override;
    std::vector<SatLit> explainConflict(
        const mcsat::MCSatTrail& trail,
        const std::vector<TheoryAtomRecord>& blockingAtoms) override;
    bool validateModel(const mcsat::MCSatTrail& trail,
                       TheorySolver::TheoryModel& outModel) override;

private:
    // Collect every variable referenced by any currently-asserted atom.
    std::unordered_set<VarId> collectVariables_() const;

    PolynomialKernel* kernel_ = nullptr;
    AlgebraBackend* algebra_ = nullptr;
    const class CoreIr* coreIr_ = nullptr;
    // mgc-H: CdcacCore is constructed lazily on first fallback use.
    // Reused across pickValue invocations so projection caches warm up.
    std::unique_ptr<CdcacCore> cdcacFallback_;

    // LIFO stack of currently-asserted atoms (level-sorted by insertion
    // order; onBacktrack truncates the tail).
    std::vector<AssertedAtom> asserted_;

    // Cached "variable id → discovery order" used as the static variable
    // order. Populated lazily on first pickNextVar.
    mutable std::vector<VarId> varOrderCache_;
    mutable bool varOrderCacheValid_ = false;

    // Phase-6 explain function: when pickValue derives a theory-valid
    // Conflict (via the simple-bound analyzer), the resulting clause
    // (list of SAT literals currently TRUE on the trail) is parked here
    // so the framework's call to explainConflict() can hand it back to
    // TheoryManager. Cleared on every pickValue invocation.
    std::vector<SatLit> pendingExplainClause_;

    // Limitation-(a) engine-side backtrack: after the first pickValue call
    // for a given (asserted_, trail) signature, run a bounded DFS over the
    // candidate set to find a COMPLETE feasible assignment. Cache it here
    // keyed by VarId so subsequent pickValue calls return the matching
    // pre-computed value. Cleared by assertLit / onBacktrack / reset.
    std::unordered_map<VarId, RealValue> cachedAssignment_;
    bool cachedAssignmentTried_ = false;  // tried DFS already this state
    bool cachedAssignmentSucceeded_ = false;
};

} // namespace nlsat
} // namespace xolver
