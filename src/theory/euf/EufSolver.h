#pragma once
#include "theory/core/TheorySolver.h"
#include "theory/euf/EufTypes.h"
#include "theory/euf/EufTermManager.h"
#include "theory/euf/IncrementalEGraph.h"
#include "theory/combination/SharedTermRegistry.h"
#include "theory/array/ArrayReasoner.h"
#include "util/SmallVector.h"
#include <vector>
#include <optional>
#include <unordered_map>
#include <unordered_set>

namespace zolver {

class EufSolver : public TheorySolver {
public:
    EufSolver();

    TheoryId id() const override { return TheoryId::EUF; }

    void push() override;
    void pop(uint32_t n) override;
    void assertLit(const TheoryAtomRecord& atom, bool value, int level, SatLit reason) override;
    void backtrackToLevel(int level) override;
    TheoryCheckResult check(TheoryLemmaStorage& lemmaDb, TheoryEffort effort = TheoryEffort::Standard) override;
    void reset() override;

    void setCoreIr(const CoreIr* ir) { coreIr_ = ir; }
    void setSharedTermRegistry(const SharedTermRegistry* reg) { sharedTermRegistry_ = reg; }

    // Enable QF_AX array reasoning. `registry` is needed so Row2/Ext lemmas
    // can create observed dynamic equality atoms before placing them in a
    // clause. Must be called before any assertLit/check.
    void enableArrays(TheoryAtomRegistry* registry) {
        arrayMode_ = true;
        arrayRegistry_ = registry;
    }

    // Nelson-Oppen combination hooks
    bool supportsCombination() const override { return true; }

    TheoryCheckResult assertInterfaceEquality(
        SharedTermId a, SharedTermId b, SatLit reason, int level) override;
    TheoryCheckResult assertInterfaceDisequality(
        SharedTermId a, SharedTermId b, SatLit reason, int level) override;

    std::vector<SharedEqualityPropagation>
    getDeducedSharedEqualities() override;

    // Nelson-Oppen arrangement query: are the two shared terms currently in the
    // SAME EUF equivalence class? Used by the combination layer (model-based
    // arrangement splitting) to decide whether an arith-equal pair of shared
    // scalars is already merged on the EUF side. Returns false (not-merged) when
    // either term is not interned as a shared constant — conservative, never
    // claims a merge that does not hold. Const because it only reads the egraph.
    bool areSharedTermsMerged(SharedTermId a, SharedTermId b) const;
    bool sharedTermsMerged(SharedTermId a, SharedTermId b) const override {
        return areSharedTermsMerged(a, b);
    }

    std::optional<TheoryModel> getModel() const override;

private:
    // Build the array/scalar model from the LIVE egraph state. Must be called
    // when the egraph reflects the satisfying assignment (i.e. at a consistent
    // Full-effort check), since merges are rolled back after solve() returns.
    std::optional<TheoryModel> buildModel() const;
    // Snapshot captured at the last consistent Full-effort check, when the
    // egraph still reflects the satisfying assignment. getModel() returns this.
    mutable std::optional<TheoryModel> modelSnapshot_;

    struct ActiveAssignment {
        int level;
        SatLit lit;
        TheoryAtomRecord atom;
        bool value;
    };

    struct ActiveDisequality {
        EufTermId lhs;
        EufTermId rhs;
        SatLit reason;
        int level;
        size_t trailIndex;
    };

    enum class BoolConstMark : uint8_t { None, True, False, Both };

    struct EClassInfo {
        BoolConstMark boolMark = BoolConstMark::None;
    };

    struct LevelSnapshot {
        int level;
        size_t trailSizeBeforeLevel;
        EGraphSnapshot egraphSnapshotBeforeLevel;
        size_t mergeQueueSize;
    };

    const CoreIr* coreIr_ = nullptr;
    const SharedTermRegistry* sharedTermRegistry_ = nullptr;
    EufTermManager termManager_;
    IncrementalEGraph egraph_;

    // Map from SharedTermId to EufTermId for interface constants
    std::unordered_map<SharedTermId, EufTermId> sharedTermToEufTerm_;
    // Shared disequalities received from combination layer
    std::vector<ActiveDisequality> sharedDisequalities_;
    int currentLevel_ = 0;

    std::vector<ActiveAssignment> trail_;
    std::vector<size_t> scopeLimits_;
    std::vector<EGraphSnapshot> scopeSnapshots_;
    std::vector<LevelSnapshot> levelSnapshots_;

    std::vector<ActiveDisequality> disequalities_;

    std::optional<TheoryConflict> pendingConflict_;
    bool pendingUnknown_ = false;

    std::vector<EClassInfo> classInfo_;
    std::deque<PendingMerge> mergeQueue_;
    EufTermId trueTerm_ = NullEufTerm;
    EufTermId falseTerm_ = NullEufTerm;

    void ensureSnapshotForLevel(int level);

    // Fallback conflict when explainEquality fails (ensures UNSAT is proven)
    std::vector<SatLit> allActiveReasons() const;

    // Build the conflict clause for a disequality (a != b) whose two sides have
    // become equal in the egraph: explainEquality(a,b) + the diseq's own reason.
    // Falls back to allActiveReasons() if the explanation is unavailable (keeps
    // UNSAT sound). Shared by the eager watch and the post-loop diseq scan.
    TheoryConflict buildDiseqConflict(const ActiveDisequality& d);

    // ZOLVER_UF_DISEQ_WATCH: eager disequality-conflict detection. When enabled,
    // after each merge in the saturation loop we check only the disequalities
    // that touch the just-merged (loser) class, catching the conflict the moment
    // it forms (shorter explanation, no wasted further congruence). Read once.
    bool diseqWatchEnabled_ = false;
    // Scratch index rebuilt per check() when the watch is on: diseq endpoint
    // term -> list of (index into the vector, 0=local diseq / 1=shared diseq).
    std::unordered_map<EufTermId, std::vector<std::pair<uint32_t, uint8_t>>> diseqByTerm_;
    void rebuildDiseqIndex();

    void initializeBoolConstants();
    void onEclassMerged(EClassId kept, EClassId killed);
    void enqueueMerge(EufTermId a, EufTermId b, const MergeReason& reason);
    EClassInfo& classInfo(EClassId id);
    static BoolConstMark mergeBoolMark(BoolConstMark a, BoolConstMark b);

    // P2: Separate interface-constant interning from original EUF expr interning
    EufTermId internSharedConstant(SharedTermId s);
    EufTermId internEufExpr(ExprId eid);

    // Constant arithmetic evaluation for #builtin terms
    void tryEvaluateBuiltin(EufTermId t);

    // QF_AX array support (layered on the shared egraph).
    bool arrayMode_ = false;
    TheoryAtomRegistry* arrayRegistry_ = nullptr;
    ArrayReasoner arrayReasoner_;
    void ensureArrayContext();
    // Active array-sort disequalities (for Extensionality lemmas).
    std::vector<ArrayReasoner::ArrayDiseq> activeArrayDiseqs() const;
};

} // namespace zolver
