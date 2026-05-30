#pragma once
#include "theory/core/TheorySolver.h"
#include "theory/euf/EufTypes.h"
#include "theory/euf/EufTermManager.h"
#include "theory/euf/IncrementalEGraph.h"
#include "theory/combination/SharedTermRegistry.h"
#include "theory/array/ArrayReasoner.h"
#include "theory/datatype/DtReasoner.h"
#include "util/SmallVector.h"
#include <vector>
#include <optional>
#include <unordered_map>
#include <unordered_set>

namespace xolver {

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

    // Registry of all parsed equality atoms — enables EUF theory propagation
    // (XOLVER_EUF_PROP): the e-graph pushes entailed equality/disequality
    // literals back to the SAT core so it need not guess each equality atom
    // (the eq_diamond exponential blowup). Distinct from arrayRegistry_/
    // dtRegistry_ (which are about minting dynamic atoms), though in array/DT
    // mode they alias the same object.
    void setEqualityAtomRegistry(TheoryAtomRegistry* r) { eqAtomRegistry_ = r; }

    // EUF theory propagation (XOLVER_EUF_PROP): after a consistent check, return
    // EUF-valid entailment clauses (¬reasons ∨ implied) for undecided equality
    // atoms that the current e-graph forces true (merged class) or false (the
    // two sides straddle an asserted disequality). Each clause is an EUF
    // tautology, so enqueuing it is sound regardless of the current assignment.
    std::vector<TheoryLemma> takeEntailmentPropagations() override;

    // Enable QF_AX array reasoning. `registry` is needed so Row2/Ext lemmas
    // can create observed dynamic equality atoms before placing them in a
    // clause. Must be called before any assertLit/check.
    void enableArrays(TheoryAtomRegistry* registry) {
        arrayMode_ = true;
        arrayRegistry_ = registry;
    }

    // Enable algebraic-datatype reasoning (QF_DT/QF_UFDT/QF_UFDTNIA). `registry`
    // is needed so injectivity / projection lemmas can mint dynamic equality
    // atoms. Mirrors enableArrays. Must be called before any assertLit/check.
    void enableDts(TheoryAtomRegistry* registry) {
        dtMode_ = true;
        dtRegistry_ = registry;
    }

    // Nelson-Oppen combination hooks
    bool supportsCombination() const override { return true; }

    TheoryCheckResult assertInterfaceEquality(
        SharedTermId a, SharedTermId b, SatLit reason, int level) override;
    TheoryCheckResult assertInterfaceDisequality(
        SharedTermId a, SharedTermId b, SatLit reason, int level) override;

    std::vector<SharedEqualityPropagation>
    getDeducedSharedEqualities() override;

    void setCareGraph(const CareGraph* cg) override { careGraph_ = cg; }

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

    // Array-index shared terms (for scoped deduced-equality propagation). Empty
    // unless array mode is on. Delegates to the ArrayReasoner.
    std::vector<SharedTermId> arrayIndexSharedTerms() const override;

    bool satComplete(std::string* reason = nullptr) const override;

    // Phase 1 combination-arrangement detector. Returns true iff there exist two
    // applications of the SAME function symbol that are NOT in the same egraph
    // class, yet every argument position is either already merged OR a pair of
    // SHARED terms the caller reports value-equal (valueEqual) — i.e. arranging
    // those shared args equal would force the applications congruent. Such a
    // pending arrangement means the combination model is NOT complete (the Wisa
    // select_format(fmt1) ≅ select_format(k) obligation). `valueEqual` is the
    // arith-model value comparison supplied by the combination layer.
    bool hasUnarrangedUfCongruence(
        const std::function<bool(SharedTermId, SharedTermId)>& valueEqual,
        std::string* reason = nullptr) const override;

    // Phase 1 arrangement (recovery). Collects the shared-term argument pairs to
    // split (a=b ∨ a≠b): the differing-but-value-equal-and-not-merged arguments
    // of same-function applications that arranging would make congruent. The
    // combination layer emits a one-time split per pair at Full effort. Finite +
    // fixed (UF apps + bridge vars are created pre-solve; arranging spawns no new
    // pairs) -> provably terminating. Shares logic with the detector above.
    std::vector<std::pair<SharedTermId, SharedTermId>> collectArrangeableUfArgPairs(
        const std::function<bool(SharedTermId, SharedTermId)>& valueEqual) const override;

    // Diagnostic / test hook: count active AssertedEquality merges whose
    // justifying literal is no longer on the trail (stale merges left by an
    // inconsistent backtrack). Must be 0 after any backtrack — exposed so tests
    // can assert the level-aware backtrack invariant directly.
    int debugCountStaleMerges() const;

private:
    // Build the array/scalar model from the LIVE egraph state. Must be called
    // when the egraph reflects the satisfying assignment (i.e. at a consistent
    // Full-effort check), since merges are rolled back after solve() returns.
    // Dispatches to buildArrayModel (QF_AX) and/or collectFunctionInterps
    // (Track 3 UF model) and returns nullopt only if both produced nothing.
    std::optional<TheoryModel> buildModel() const;
    // Array/scalar interpretation builder (QF_AX). Fills model.arrayInterps and
    // scalar token assignments; no-op when there are no array variables.
    void buildArrayModel(TheoryModel& model) const;
    // Token-keyed UF function interpretations (Track 3, XOLVER_EUF_UF_MODEL).
    // One FuncInterp per uninterpreted function symbol, keyed on argument
    // class-tokens; TheoryManager::getModel remaps the tokens to the bare-rational
    // keys the ArithModelValidator expects. Also emits scalar var -> class-token
    // assignments so that remap can resolve each token to its arith value.
    void collectFunctionInterps(TheoryModel& model) const;
    // Canonical class token for the ArithModelValidator namespace: numeric
    // literal -> "#n:<rational>", bool literal -> "#b:1"/"#b:0", else opaque
    // per-class marker "@e<rep>". Shared by buildArrayModel + collectFunctionInterps.
    std::string classToken(EufTermId t) const;
    // Sort name as the validator expects ("Int"/"Real"/"Bool"/"U<id>").
    std::string sortName(SortId s) const;
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

    // Egraph state at a decision-level boundary: egraphBefore is the egraph
    // snapshot captured the moment check() begins processing merges of `level`
    // (i.e. AFTER all lower-level merges are applied). Recorded only for levels
    // that actually produce merges; entries are kept sorted ascending by level.
    // Backtrack to target restores the boundary of the SMALLEST level > target
    // (whose egraphBefore == state after all level-≤target merges), which works
    // because the saturation applies merges in ascending level order so the
    // egraph's size-based undo trail is level-monotonic.
    struct EgraphBoundary {
        int level;
        EGraphSnapshot egraphBefore;
    };

    const CoreIr* coreIr_ = nullptr;
    const SharedTermRegistry* sharedTermRegistry_ = nullptr;
    const CareGraph* careGraph_ = nullptr;  // XOLVER_COMB_CAREGRAPH, set by TheoryManager
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
    std::vector<EgraphBoundary> egraphBoundaries_;

    std::vector<ActiveDisequality> disequalities_;

    std::optional<TheoryConflict> pendingConflict_;
    bool pendingUnknown_ = false;

    std::vector<EClassInfo> classInfo_;
    std::deque<PendingMerge> mergeQueue_;
    EufTermId trueTerm_ = NullEufTerm;
    EufTermId falseTerm_ = NullEufTerm;

    // Record an egraph boundary for `level` (state before its merges) if not
    // already recorded. Called from check() at each level transition.
    void recordEgraphBoundary(int level);

    // Fallback conflict when explainEquality fails (ensures UNSAT is proven)
    std::vector<SatLit> allActiveReasons() const;

    // Build the conflict clause for a disequality (a != b) whose two sides have
    // become equal in the egraph: explainEquality(a,b) + the diseq's own reason.
    // Falls back to allActiveReasons() if the explanation is unavailable (keeps
    // UNSAT sound). Shared by the eager watch and the post-loop diseq scan.
    TheoryConflict buildDiseqConflict(const ActiveDisequality& d);

    // XOLVER_UF_DISEQ_WATCH: eager disequality-conflict detection. When enabled,
    // after each merge in the saturation loop we check only the disequalities
    // that touch the just-merged (loser) class, catching the conflict the moment
    // it forms (shorter explanation, no wasted further congruence). Read once.
    // Re-enabled after the N-O proof forest + level-aware backtrack made
    // mid-saturation explainEquality sound (the bug that forced the revert).
    bool diseqWatchEnabled_ = false;
    // XOLVER_EUF_PROP: enable EUF theory propagation (entailed equality/diseq
    // literals lifted to SAT). Read once in the constructor.
    bool eufPropEnabled_ = false;
    // XOLVER_EUF_UF_MODEL (Track 3): build token-keyed function interpretations
    // for non-array combination (UFNIA/UFNRA) so the ArithModelValidator can
    // CONFIRM combination sats (UFApply table lookup) instead of flooring them
    // to unknown on Indeterminate. Scoped to combination mode (sharedTermRegistry_)
    // since pure QF_UF already gets functionInterps from CandidateModelSearch.
    // Read once in the constructor.
    bool ufModelEnabled_ = false;
    // Registry of all parsed equality atoms (set in TheoryFactory). Needed to
    // enumerate UNDECIDED equality atoms for propagation — assertLit only ever
    // sees assigned ones.
    TheoryAtomRegistry* eqAtomRegistry_ = nullptr;
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

    // Algebraic-datatype support (layered on the same shared egraph).
    bool dtMode_ = false;
    TheoryAtomRegistry* dtRegistry_ = nullptr;
    DtReasoner dtReasoner_;
    void ensureDtContext();
};

} // namespace xolver
