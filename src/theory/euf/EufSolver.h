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
    ~EufSolver();

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
        // EUF e-propagation in combination needs the equality-atom registry to
        // scan EUF Eq atoms; array logics never set it via the single-theory
        // path, so wire it here too (same registry). Inert unless EUF_PROP is
        // drained in combination (TheoryManager gate).
        if (!eqAtomRegistry_) eqAtomRegistry_ = registry;
    }

    // Enable algebraic-datatype reasoning (QF_DT/QF_UFDT/QF_UFDTNIA). `registry`
    // is needed so injectivity / projection lemmas can mint dynamic equality
    // atoms. Mirrors enableArrays. Must be called before any assertLit/check.
    void enableDts(TheoryAtomRegistry* registry) {
        dtMode_ = true;
        dtRegistry_ = registry;
    }

    // DT model re-validator hook: original-formula assertions to re-evaluate
    // at sat time using the live e-graph. Pointer must outlive this solver
    // (Solver::originalAssertions_ provides it). When set, EufSolver::check
    // at Full-effort runs DtModelValidator after modelFullyDetermined; if any
    // assertion evaluates to DEFINITELY false under the candidate e-graph
    // state, return Unknown (sound floor for the QF_DT blocksworld false-SAT
    // residual class). SMT-LIB semantics respected: selector-on-wrong-ctor
    // is Indeterminate, not Violated.
    void setOriginalAssertions(const std::vector<ExprId>* p) {
        originalAssertionsForDtValidate_ = p;
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
    std::vector<SharedTermId> arrayValueSharedTerms() const override;

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

    // UFE INVARIANT CHECKER (XOLVER_DIAG_PF_INV / XOLVER_ASSERT_PF_INV gated).
    // Walks every reachable edge in the proof forest; for each AssertedEquality
    // edge, verifies its literal is currently asserted on trail at the same
    // polarity. For each Congruence edge, verifies every (a_i, b_i) in
    // argPairs is currently same-class in the egraph. Returns true if all
    // invariants hold; logs the first violation to stderr when DIAG is on, and
    // (when ASSERT is on) aborts so the bisection lands on the operation that
    // broke the invariant. This is the soundness gate for XOLVER_UF_DISEQ_WATCH:
    // the watcher's conflict clause only makes sense if proof-forest labels are
    // coherent with the current trail.
    bool checkProofForestInvariants(const char* where) const;

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
    // XOLVER_EUF_MINLEVEL_HEAP (default-OFF, array-deep B2): use a level-bucketed map to drain
    // the saturation mergeQueue_ in O(n log L) instead of the O(n^2) linear
    // min-level scan. Same processing order; targets QF_ANIA/QF_AX-swap blowup.
    // Read once in the constructor.
    bool minLevelHeapEnabled_ = false;
    // XOLVER_AX_STORE_MODEL (default-OFF, array-deep A1): store-aware array model
    // construction (follow store chains so a store-defined array inherits its
    // base's entries). Verdict-sound; recovers the storecomm sat class.
    bool storeModelEnabled_ = false;
    // XOLVER_EUF_INCREMENTAL_PROP (Phase A, agent/euf-deep): incremental
    // entailment-propagation scan. Instead of re-iterating the full EUF Eq atom
    // registry every cb_propagate, track new-since-last-call merges and scan
    // only atoms whose term touches a newly-merged class. Sound by construction:
    // - On backtrack the next call forces a full sweep (atom-assignment also
    //   changed; merges rolled back).
    // - After a full sweep, subsequent calls use incremental.
    // - The class-touch index is maintained lazily (term → atom-indices).
    // Verify gate XOLVER_EUF_INCREMENTAL_PROP_VERIFY=1 runs BOTH full and
    // incremental and asserts the output set is equal (debug oracle).
    // Read once.
    bool eufIncrementalProp_ = false;
    bool eufIncrementalVerify_ = false;
    // XOLVER_EUF_PROP_DEDUP (Phase A v2): skip atoms whose entailment lemma we
    // ALREADY emitted at level <= currentLevel (SAT's lemmaDb still holds them).
    // On backtrack, drop emissions at level > target. Same emission set as full
    // sweep modulo duplicates → strict win on duplicate-heavy workloads. Sound
    // by construction (SAT only ever needs each lemma once until backtrack).
    bool eufPropDedup_ = false;
    // emittedAtomLevel_[recIdx] = level at which we last emitted a lemma for
    // this rec; -1 = never. Cleared on backtrack to entries > target.
    std::vector<int> emittedAtomLevel_;
    // term-indexed atom-registry: termToEntailmentAtomIdx_[tid] = vector of
    // recs indices whose lhs OR rhs is this term. Built lazily, extended
    // monotonically — recs never shrink.
    std::vector<std::vector<size_t>> termToEntailmentAtomIdx_;
    size_t lastIndexedEntailmentRecCount_ = 0;
    // egraph mergeRecord watermark — new merges since last propagation call
    // are scanned to compute the dirty atom-index set.
    size_t lastSeenMergeRecord_ = 0;
    // Set on backtrack — next propagation call must do a full sweep (assigned
    // set changed, mergeRecord count regressed).
    bool forceFullEntailmentScan_ = true;

    // XOLVER_EUF_HOTPROFILE (default-OFF, agent/eqna-2 E2/E3 profile task):
    // lightweight per-check counters + chrono accumulators. Dump on dtor when
    // any call happened. Used to triage QG-classification / eq_diamond hot
    // path (perf+flamegraph not available on WSL).
    bool hotProfileEnabled_ = false;
    // XOLVER_AX_FIXPOINT (L3, default-OFF): re-run the array-axiom passes to
    // fixpoint after the main saturation, so nested read-over-write resolves
    // within one check() instead of one nesting level per CDCL(T) round.
    bool arrayFixpointEnabled_ = false;
    struct EufHotProfile {
        uint64_t checkCalls = 0;
        uint64_t mergesProcessed = 0;       // saturation merges drained
        uint64_t explainCalls = 0;          // explainEquality invocations
        uint64_t entailmentScanRecs = 0;    // recs iterated in takeEntailmentPropagations
        uint64_t entailmentEmitted = 0;     // lemmas emitted by entailment scan
        int64_t  checkUs = 0;               // total wall in check()
        int64_t  saturationUs = 0;          // wall inside saturation loop
        int64_t  explainUs = 0;             // wall inside explainEquality
        int64_t  entailmentUs = 0;          // wall inside takeEntailmentPropagations
        int64_t  registerSigUs = 0;         // wall inside registerPendingSignatures
    };
    EufHotProfile hotProfile_;
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
    void tryEvaluateBuiltin(EufTermId t, int level);

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
    const std::vector<ExprId>* originalAssertionsForDtValidate_ = nullptr;
};

} // namespace xolver
