#pragma once

#include "theory/core/TheorySolver.h"
#include "theory/core/TheoryAssignmentView.h"
#include "theory/combination/SharedTermRegistry.h"
#include "theory/combination/SharedEqualityManager.h"
#include <memory>
#include <vector>
#include <unordered_map>
#include <unordered_set>
#include <deque>

namespace nlcolver {

class TheoryAtomRegistry;
class SatSolver;

class TheoryManager {
public:
    void registerSolver(std::unique_ptr<TheorySolver> solver);
    void clearSolvers();

    void setCombinationMode(bool enabled) { combinationMode_ = enabled; }
    bool isCombinationMode() const { return combinationMode_; }

    void setNonConvexMode(bool enabled) { nonConvexMode_ = enabled; }
    bool isNonConvexMode() const { return nonConvexMode_; }

    void setArrangementComplete(bool v) { arrangementComplete_ = v; }
    bool isArrangementComplete() const { return arrangementComplete_; }

    void assertTheoryLit(const TheoryAtomRecord& atom, SatLit assignedLit, int level);
    void backtrackToLevel(int level);
    TheoryCheckResult check(TheoryLemmaDatabase& lemmaDb, TheoryEffort effort = TheoryEffort::Standard);

    void setRegistry(TheoryAtomRegistry* registry) { registry_ = registry; }
    void setAssignmentView(const TheoryAssignmentView* view) { assignmentView_ = view; }
    void setSharedTermRegistry(SharedTermRegistry* reg) { sharedTermRegistry_ = reg; }

    SharedTermRegistry* sharedTermRegistry() { return sharedTermRegistry_; }
    const SharedTermRegistry* sharedTermRegistry() const { return sharedTermRegistry_; }

    /** Aggregate models from all registered theory solvers. */
    std::optional<TheorySolver::TheoryModel> getModel() const;

private:
    std::vector<std::unique_ptr<TheorySolver>> solvers_;
    std::unordered_map<TheoryId, TheorySolver*> solverByTheory_;

    bool combinationMode_ = false;
    bool nonConvexMode_ = false;
    bool arrangementComplete_ = true;
    TheoryAtomRegistry* registry_ = nullptr;
    const TheoryAssignmentView* assignmentView_ = nullptr;
    SharedTermRegistry* sharedTermRegistry_ = nullptr;

    SharedEqualityManager sharedEqMgr_;

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

} // namespace nlcolver
