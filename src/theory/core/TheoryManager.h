#pragma once

#include "theory/core/TheorySolver.h"
#include "theory/core/TheoryAssignmentView.h"
#include "theory/core/TheoryPropagatorCallbacks.h"
#include "theory/combination/SharedTermRegistry.h"
#include "theory/combination/SharedEqualityManager.h"
#include "theory/combination/CareGraph.h"
#include "theory/combination/ConflictMinimizer.h"
#include <memory>
#include <vector>
#include <unordered_map>
#include <unordered_set>
#include <deque>

namespace zolver {

class TheoryAtomRegistry;
class SatSolver;

class TheoryManager : public TheoryPropagationCallbacks {
public:
    void registerSolver(std::unique_ptr<TheorySolver> solver);
    void clearSolvers();

    void setCombinationMode(bool enabled) { combinationMode_ = enabled; }
    bool isCombinationMode() const override { return combinationMode_; }

    void setNonConvexMode(bool enabled) { nonConvexMode_ = enabled; }
    bool isNonConvexMode() const { return nonConvexMode_; }

    void setArrangementComplete(bool v) { arrangementComplete_ = v; }
    bool isArrangementComplete() const { return arrangementComplete_; }

    // Scopes model-based arrangement splitting to the array combination logics
    // (QF_ALRA/ALIA/AUFLRA/AUFLIA). Off by default to limit blast radius — the
    // splitting only fires when both an EUF (array) solver and an arith solver
    // share scalar index/element terms.
    void setArrayCombinationMode(bool v) { arrayCombinationMode_ = v; }
    bool isArrayCombinationMode() const { return arrayCombinationMode_; }

    void assertTheoryLit(const TheoryAtomRecord& atom, SatLit assignedLit, int level) override;
    void backtrackToLevel(int level) override;
    TheoryCheckResult check(TheoryLemmaStorage& lemmaDb, TheoryEffort effort = TheoryEffort::Standard) override;

    void setRegistry(TheoryAtomRegistry* registry) { registry_ = registry; }
    void setAssignmentView(TheoryAssignmentView* view) override { assignmentView_ = view; }
    void setSharedTermRegistry(SharedTermRegistry* reg) { sharedTermRegistry_ = reg; }

    // Aggregate statistics collected during check() calls
    struct AggregateStats {
        int64_t checkCalls = 0;
        int64_t conflicts = 0;
        int64_t lemmas = 0;
        int64_t propagations = 0;
        int64_t totalConflictSize = 0;
        int64_t maxConflictSize = 0;
    };
    const AggregateStats& aggregateStats() const { return aggStats_; }
    std::vector<std::string> activeTheoryNames() const;

    SharedTermRegistry* sharedTermRegistry() { return sharedTermRegistry_; }
    const SharedTermRegistry* sharedTermRegistry() const { return sharedTermRegistry_; }

    /** Aggregate models from all registered theory solvers. */
    std::optional<TheorySolver::TheoryModel> getModel() const;

    /**
     * Collect all linear atoms whose current SAT assignment makes them
     * effectively true (including negated atoms, whose effective relation
     * is the negation of the original relation).
     */
    std::vector<ActiveLinearConstraint> collectActiveLinearConstraints() const;

private:
    std::vector<std::unique_ptr<TheorySolver>> solvers_;
    std::unordered_map<TheoryId, TheorySolver*> solverByTheory_;

    bool combinationMode_ = false;
    bool nonConvexMode_ = false;
    bool arrangementComplete_ = true;
    bool arrayCombinationMode_ = false;
    // Stable dedup of arrangement splits already emitted (per canonical pair
    // key). Bounded by #shared-scalar pairs -> guarantees termination.
    std::unordered_set<uint64_t> emittedArrangementSplits_;
    TheoryAtomRegistry* registry_ = nullptr;
    TheoryAssignmentView* assignmentView_ = nullptr;
    SharedTermRegistry* sharedTermRegistry_ = nullptr;
    AggregateStats aggStats_;

    SharedEqualityManager sharedEqMgr_;

    // Demand-driven care graph (ZOLVER_COMB_CAREGRAPH, default OFF). Built once
    // per solve from the purified IR; prunes the O(n^2) shared-pair loops
    // (deduced-equality propagation + model-based arrangement splitting) to
    // pairs that can actually fire a theory inference. Under-approximation =>
    // sound (lost completeness caught by ModelValidator, never wrong UNSAT).
    CareGraph careGraph_;
    bool careGraphEnabled_ = false;
    bool careGraphEnvChecked_ = false;
    void ensureCareGraph();

    // Theory-agnostic combination conflict/lemma minimization (ZOLVER_SAT_MIN,
    // default OFF). Dedups literals in interface/theory conflicts and lemmas.
    // Always sound (dedup preserves the clause's literal set).
    bool satMinEnabled_ = false;
    bool satMinEnvChecked_ = false;
    bool useSatMin();

    // Model-based theory combination for the non-convex combined logics
    // (ZOLVER_COMB_MODEL_BASED, default OFF). Extends the array-only arrangement
    // splitting to QF_UFLIA/UFNIA/UFNRA: at Full effort, force the Nelson-Oppen
    // arrangement over shared scalars to be CLOSED before reporting Sat, so the
    // combination cannot return a per-theory-consistent-but-globally-inconsistent
    // model (the existing false-SAT class). The split is a tautology over a
    // shared-equality atom, so it is sound by construction; the theories react
    // through the already-validated interface (dis)equality paths.
    bool modelBasedEnabled_ = false;
    bool modelBasedEnvChecked_ = false;
    bool useModelBased();

    struct PendingSharedEqEvent {
        SharedTermId a;
        SharedTermId b;
        bool isEquality;
        SatLit reasonLit;
        int decisionLevel;
    };
    std::deque<PendingSharedEqEvent> pendingSharedEqEvents_;

    struct LevelSnapshot {
        int level;
        SharedEqualitySnapshot sharedEqSnap;
    };
    std::vector<LevelSnapshot> snapshots_;

    struct ReportedPropKey {
        TheoryId source;
        SharedTermId a;
        SharedTermId b;
        bool operator==(const ReportedPropKey& o) const {
            return source == o.source && a == o.a && b == o.b;
        }
    };
    struct ReportedPropKeyHash {
        size_t operator()(const ReportedPropKey& k) const {
            size_t h = std::hash<uint8_t>{}(static_cast<uint8_t>(k.source));
            h = h * 31 + std::hash<uint32_t>{}(k.a);
            h = h * 31 + std::hash<uint32_t>{}(k.b);
            return h;
        }
    };
    std::unordered_set<ReportedPropKey, ReportedPropKeyHash> deducedEqCache_;

    std::vector<TheorySolver*> solversOwning(SharedTermId a, SharedTermId b) const;
    void ensureSnapshotForLevel(int level);
    LevelSnapshot& snapshotForLevel(int level);
    void discardSnapshotsAbove(int level);
};

} // namespace zolver
