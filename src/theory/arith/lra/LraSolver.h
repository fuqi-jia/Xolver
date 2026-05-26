#pragma once

#include "theory/arith/ArithSolverBase.h"
#include "theory/core/TheoryAtomRegistry.h"
#include "theory/arith/linear/LinearAtomManager.h"
#include "theory/combination/SharedTermRegistry.h"
#include "GeneralSimplex.h"
#include "LraPropagationEngine.h"
#include <gmpxx.h>
#include <optional>
#include <unordered_map>
#include <vector>
#include <string>

namespace zolver {

class LraSolver : public ArithSolverBase {
public:
    LraSolver();
    ~LraSolver();

    TheoryId id() const override { return TheoryId::LRA; }

    // LRA keeps its own incremental cursor trail (theoryTrail_ +
    // appliedCursor_) with simplex-specific entry data, so it overrides
    // assertLit and routes push/pop/backtrack/reset through the base
    // hooks. check() is the base default driving a single core reasoner.
    void assertLit(const TheoryAtomRecord& atom, bool value, int level, SatLit assertedLit) override;

    void setCoreIr(const CoreIr* ir) { coreIr_ = ir; }
    void setSharedTermRegistry(const SharedTermRegistry* reg) { sharedTermRegistry_ = reg; }
    void setRegistry(TheoryAtomRegistry* reg) { registry_ = reg; }

    // Nelson-Oppen combination hooks
    bool supportsCombination() const override { return true; }

    TheoryCheckResult assertInterfaceEquality(
        SharedTermId a, SharedTermId b, SatLit reason, int level) override;
    TheoryCheckResult assertInterfaceDisequality(
        SharedTermId a, SharedTermId b, SatLit reason, int level) override;

    std::vector<SharedEqualityPropagation>
    getDeducedSharedEqualities() override;

    std::optional<TheoryModel> getModel() const override;

protected:
    void onPush() override;
    void onPop(uint32_t n) override;
    void onBacktrack(int targetLevel) override;
    void onReset() override;

private:
    // Single core reasoner stage (Phase 2): incremental replay + interface
    // equalities + simplex + disequality split + propagation. Always
    // yields a verdict (never nullopt-continue).
    std::optional<TheoryCheckResult> stageCore(TheoryLemmaStorage& lemmaDb, TheoryEffort effort);

    GeneralSimplex gs_;
    LinearAtomManager manager_;

    // -------------------------------------------------------------------------
    // Incremental trail (Phase 1)
    // -------------------------------------------------------------------------
    struct LraTrailEntry {
        int level;
        SatLit lit;
        TheoryAtomRecord atom;
        bool value;
        int auxVar = -1;  // pre-computed aux var for this linear form
        bool isDiseq = false;
    };
    std::vector<LraTrailEntry> theoryTrail_;
    size_t appliedCursor_ = 0;
    std::optional<TheoryCheckResult> pendingConflict_;

    bool applyEntryToSimplex(const LraTrailEntry& e);

    // -------------------------------------------------------------------------
    // Disequality handling
    // -------------------------------------------------------------------------
    struct DiseqInfo {
        int auxVar;
        LinearFormKey lhs;
        mpq_class rhs;
        SatLit lit;
        int level;
    };

    std::vector<DiseqInfo> activeDisequalities_;

    // -------------------------------------------------------------------------
    // Interface equalities / disequalities (Nelson-Oppen)
    // -------------------------------------------------------------------------
    struct InterfaceEq {
        SharedTermId a;
        SharedTermId b;
        SatLit reason;
        int level;
    };
    std::vector<InterfaceEq> interfaceEqualities_;
    std::vector<InterfaceEq> interfaceDisequalities_;
    int currentLevel_ = 0;

    // Map from (a,b) canonical key to auxiliary var index for x - y
    std::unordered_map<uint64_t, int> interfaceEqAuxVars_;

    const CoreIr* coreIr_ = nullptr;
    const SharedTermRegistry* sharedTermRegistry_ = nullptr;

    // Map from SharedTermId to variable name for simplex
    std::unordered_map<SharedTermId, std::string> sharedTermToVarName_;

    std::string getVarNameForSharedTerm(SharedTermId s);
    int getOrCreateInterfaceEqAuxVar(SharedTermId a, SharedTermId b);

    // If the asserted linear (in)equality atoms entail that the two shared
    // terms a and b are equal — via an explicit 2-var equality atom
    // (c*x - c*y = 0) or two complementary inequalities pinning the difference
    // to 0 (x<=y ∧ y<=x) — return the reason literals of the pinning atoms.
    // Empty if no such entailment. Used to propagate implied shared equalities
    // and to refute an interface disequality x!=y that contradicts x=y.
    std::vector<SatLit> assertedVarEqualityReason(SharedTermId a, SharedTermId b) const;

    TheoryAtomRegistry* registry_ = nullptr;

    std::vector<SatLit> allActiveReasons() const;

    // -------------------------------------------------------------------------
    // Phase C: bound propagation
    // -------------------------------------------------------------------------
    LraPropagationEngine propagationEngine_;

    struct AuxFormInfo {
        LinearFormKey lhs;
        mpq_class rhs;
    };
    std::unordered_map<int, AuxFormInfo> auxFormInfo_;

    std::optional<TheoryLemma> tryConvertDerivedBound(
        const LraPropagationEngine::ExplainedBound& eb) const;

#ifdef ZOLVER_LRA_PROFILE
    struct ProfileStats {
        int solveCount = 0;
        int checkCalls = 0;
        int64_t totalActiveLiterals = 0;
        int maxActiveLiterals = 0;
        int prevActiveCount = 0;
        int64_t totalNewLiterals = 0;
        int64_t resetTimeUs = 0;
        int64_t assertBoundTimeUs = 0;
        int64_t simplexCheckTimeUs = 0;
        int fallbackConflictCount = 0;
        int64_t totalConflictSize = 0;
        int maxConflictSize = 0;
        int rowConflictCount = 0;
        int immediateConflictCount = 0;
        int disequalitySplitCount = 0;
        int64_t totalPivotCount = 0;
        int64_t mpqOpTimeUs = 0;
        int maxCoeffNumBits = 0;
        int maxCoeffDenBits = 0;
        int64_t totalCoeffNumBits = 0;
        int64_t totalCoeffDenBits = 0;
        int64_t totalCoeffSamples = 0;

        void resetForNewSolve() {
            solveCount++;
            checkCalls = 0;
            totalActiveLiterals = 0;
            maxActiveLiterals = 0;
            prevActiveCount = 0;
            totalNewLiterals = 0;
            resetTimeUs = 0;
            assertBoundTimeUs = 0;
            simplexCheckTimeUs = 0;
            fallbackConflictCount = 0;
            totalConflictSize = 0;
            maxConflictSize = 0;
            rowConflictCount = 0;
            immediateConflictCount = 0;
            disequalitySplitCount = 0;
            totalPivotCount = 0;
        }
        void dump() const;
    };
    mutable ProfileStats profile_;
#endif
};

} // namespace zolver
