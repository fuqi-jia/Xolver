#pragma once

#include "search/arith/ArithSolverBase.h"
#include "search/coordination/TheoryAtomRegistry.h"
#include "search/linear/LinearAtomManager.h"
#include "search/combination/SharedTermRegistry.h"
#include "search/lra/GeneralSimplex.h"
#include "search/lra/LraPropagationEngine.h"
#include <gmpxx.h>
#include <optional>
#include <unordered_map>
#include <unordered_set>
#include <vector>
#include <string>

namespace xolver {

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
    void restoreRootLiteral(const TheoryAtomRecord& atom, bool value, SatLit lit) override {
        assertLit(atom, value, 0, lit);
    }

    // setNativeTerms / setSharedTermRegistry now live in ArithSolverBase (hoisted
    // 2026-06-04). The NativeTerms* / SharedTermRegistry* fields are protected on
    // the base.
    void setRegistry(TheoryAtomRegistry* reg) { registry_ = reg; }

    // Nelson-Oppen combination hooks
    bool supportsCombination() const override { return true; }

    TheoryCheckResult assertInterfaceEquality(
        SharedTermId a, SharedTermId b, SatLit reason, int level) override;
    TheoryCheckResult assertInterfaceDisequality(
        SharedTermId a, SharedTermId b, SatLit reason, int level) override;

    std::vector<SharedEqualityPropagation>
    getDeducedSharedEqualities() override;

    std::optional<RealValue> sharedTermArithValue(SharedTermId s) const override;


    std::optional<TheoryModel> getModel() const override;

    // Drain sound Farkas row-propagations
    // (reasons ⟹ impliedBound) buffered during the last check() so the SAT
    // propagator can install them during search. Entailment-tagged only.
    std::vector<TheoryLemma> takeEntailmentPropagations() override;

    // cb_decide feasibility heuristic: is the bound atom `v` true at the current
    // simplex point? double eval (allocation-free hot path); heuristic only.
    std::optional<bool> evalAtomAtModel(SatVar v) override;

protected:
    void onPush() override;
    void onPop(uint32_t n) override;
    void onBacktrack(int targetLevel) override;
    void onReset() override;

private:
#ifdef XOLVER_ENABLE_PROOFS
    // Phase C: push an la_generic Farkas certificate (the multipliers GeneralSimplex
    // captured — unit for an immediate conflict, |row coeffs| for a row conflict)
    // for the current simplex conflict to the active proof sink. No-op off the
    // proof path. Called at every conflict-emission point.
    void pushLraFarkasCert();
#endif

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
    struct TrailKey {
        SatVar operator()(const LraTrailEntry& entry) const { return entry.atom.satVar; }
    };
    incremental::IndexedContext<LraTrailEntry, TrailKey> theoryTrail_;
    size_t appliedCursor_ = 0;
    std::optional<TheoryCheckResult> pendingConflict_;

    void clearActiveSources();
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

    // Materialize the infinitesimal without collapsing a decided disequality.
    mpq_class modelDelta() const;

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

    // nativeTerms_, sharedTermRegistry_ hoisted to ArithSolverBase (2026-06-04).

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

    struct ColumnForm {
        LinearFormKey lhs;
        mpq_class rhs;
    };
    std::unordered_map<int, ColumnForm> columnForms_;

    // Build a SOUND propagation clause (¬reason₁ ∨ ... ∨ impliedBound) carrying
    // the Farkas reasons, tagged Entailment. Safe to give the SAT solver during
    // search; the propagator verifies it is unit/falsified.
    std::optional<TheoryLemma> buildEntailmentLemma(
        const LraPropagationEngine::ExplainedBound& eb,
        const std::vector<int8_t>& activeValues,
        const std::unordered_set<uint64_t>& queuedConclusions);

    // Buffer of this check's entailment propagations.
    std::vector<TheoryLemma> entailmentProps_;

#ifdef XOLVER_LRA_PROFILE
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

} // namespace xolver
