#pragma once
#include "theory/TheorySolver.h"
#include "theory/euf/EufTypes.h"
#include "theory/euf/EufTermManager.h"
#include "theory/euf/IncrementalEGraph.h"
#include "theory/combination/SharedTermRegistry.h"
#include "util/SmallVector.h"
#include <vector>
#include <optional>
#include <unordered_map>
#include <unordered_set>

namespace nlcolver {

class EufSolver : public TheorySolver {
public:
    EufSolver();

    TheoryId id() const override { return TheoryId::EUF; }

    void push() override;
    void pop(uint32_t n) override;
    void assertLit(const TheoryAtomRecord& atom, bool value, int level, SatLit reason) override;
    void backtrackToLevel(int level) override;
    TheoryCheckResult check(TheoryLemmaDatabase& lemmaDb) override;
    void reset() override;

    void setCoreIr(const CoreIr* ir) { coreIr_ = ir; }
    void setSharedTermRegistry(const SharedTermRegistry* reg) { sharedTermRegistry_ = reg; }

    // Nelson-Oppen combination hooks
    bool supportsCombination() const override { return true; }

    TheoryCheckResult assertInterfaceEquality(
        SharedTermId a, SharedTermId b, SatLit reason, int level) override;
    TheoryCheckResult assertInterfaceDisequality(
        SharedTermId a, SharedTermId b, SatLit reason, int level) override;

    std::vector<SharedEqualityPropagation>
    getDeducedSharedEqualities() override;

private:
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
        SmallVector<IteId, 4> condUses;
        SmallVector<IteId, 4> thenUses;
        SmallVector<IteId, 4> elseUses;
        BoolConstMark boolMark = BoolConstMark::None;
    };

    struct IteOccMoveTrail {
        EClassId kept, killed;
        size_t keptCondOldSize, keptThenOldSize, keptElseOldSize;
        size_t killedCondOldSize, killedThenOldSize, killedElseOldSize;
        size_t movedCondCount, movedThenCount, movedElseCount;
        BoolConstMark keptOldMark, killedOldMark;
    };

    struct IteSnapshot {
        size_t occMoveTrailSize;
        size_t mergeQueueSize;
        size_t nextTermToScan;
    };

    struct LevelSnapshot {
        int level;
        size_t trailSizeBeforeLevel;
        EGraphSnapshot egraphSnapshotBeforeLevel;
        IteSnapshot iteSnapshot;
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

    // ---- ITE incremental saturation state ----
    struct IteRecord {
        EufTermId result;
        EufTermId cond;
        EufTermId thenTerm;
        EufTermId elseTerm;
    };
    std::vector<IteRecord> iteRecords_;
    std::unordered_map<EufTermId, IteId> iteOfResult_;
    std::vector<EClassInfo> classInfo_;
    std::vector<IteOccMoveTrail> iteOccMoveTrail_;
    std::deque<PendingMerge> mergeQueue_;   // ITE + congruence merges
    size_t nextTermToScan_ = 0;
    EufTermId trueTerm_ = NullEufTerm;
    EufTermId falseTerm_ = NullEufTerm;

    void ensureSnapshotForLevel(int level);

    // ITE helpers
    void initializeBoolConstants();
    void registerNewIteTerms();
    void registerIte(EufTermId result, EufTermId cond,
                     EufTermId thenTerm, EufTermId elseTerm);
    void tryFireIte(IteId id);
    void onEclassMerged(EClassId kept, EClassId killed);
    void enqueueMerge(EufTermId a, EufTermId b, const MergeReason& reason);
    EClassInfo& classInfo(EClassId id);
    static BoolConstMark mergeBoolMark(BoolConstMark a, BoolConstMark b);

    // P2: Separate interface-constant interning from original EUF expr interning
    EufTermId internSharedConstant(SharedTermId s);
    EufTermId internEufExpr(ExprId eid);
};

} // namespace nlcolver
