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

    std::optional<RealValue> sharedTermArithValue(SharedTermId s) const override;

    void allowInterfaceDiseqModelBranch(SharedTermId a, SharedTermId b) override;

    std::optional<TheoryModel> getModel() const override;

    // XOLVER_LRA_PROP (default OFF): drain sound Farkas row-propagations
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

    // Canonical (a,b) keys whose decided interface disequality this solver is
    // authorized to model-branch (set by the combination layer's arrangement
    // split). Persists across backtrack/reset — it is a static property of the
    // pair, not of the search state.
    std::unordered_set<uint64_t> diseqBranchAuthorized_;

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

    // Build a SOUND propagation clause (¬reason₁ ∨ ... ∨ impliedBound) carrying
    // the Farkas reasons, tagged Entailment. Safe to give the SAT solver during
    // search (XOLVER_LRA_PROP); the propagator verifies it is unit/falsified.
    std::optional<TheoryLemma> buildEntailmentLemma(
        const LraPropagationEngine::ExplainedBound& eb) const;

    // XOLVER_LRA_PROP gate (read once) + this-check buffer of entailment props.
    bool lraPropEnabled_ = false;
    std::vector<TheoryLemma> entailmentProps_;

    // XOLVER_SIMPLEX_IMPLIED_EQ (default OFF): emit transitively-closed and/or
    // polyhedrally-implied shared equalities through the Nelson-Oppen channel,
    // not just the directly-asserted 2-var pairs the per-pair detector finds.
    // Step 1 (transitivity): closes chains of asserted equalities (x=z and z=y
    // -> x=y) over the shared-var graph; chain reasons are the union of the
    // edge SatLits along the BFS path. Step 2 (polyhedral): aux-var tight-bound
    // query — emits a=b when the simplex bound-propagation engine proves
    // (a-b) in [0,0] across the whole polyhedron (every feasible model). Read
    // once in the ctor.
    bool impliedEqEnabled_ = false;

    // cb_decide feasibility-eval cache (v2): per atom satVar, the STATIC linear
    // form as (var-NAME, double coeff) pairs + double rhs + relation, resolved
    // ONCE from the atom record (the expensive findBySatVar / payload step).
    // Eval resolves each var's simplex index FRESH via an O(1) findVarIndex —
    // we cache the resolution, never the index, so a lazily-registered or
    // backtracked var can't produce a stale out-of-bounds index. Atoms whose
    // vars aren't in the simplex yet are skipped O(1) (first missing var exits).
    struct AtomEvalForm {
        bool isLinear = false;  // resolvable bound atom?
        std::vector<std::pair<std::string, double>> terms;  // (var name, coeff)
        double rhs = 0.0;
        Relation rel = Relation::Leq;
    };
    std::unordered_map<SatVar, AtomEvalForm> atomEvalCache_;

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
