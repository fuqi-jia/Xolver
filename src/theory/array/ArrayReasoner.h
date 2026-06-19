#pragma once

#include "expr/types.h"
#include "theory/euf/EufTypes.h"
#include "theory/core/TheoryAtomTypes.h"
#include <vector>
#include <deque>
#include <unordered_set>
#include <unordered_map>
#include <optional>
#include <functional>
#include <cstdint>

namespace xolver {

class EufTermManager;
class IncrementalEGraph;
class CoreIr;
class TheoryAtomRegistry;
class SharedTermRegistry;
struct PendingMerge;

// ---------------------------------------------------------------------------
// ArrayReasoner — QF_AX array axiom instantiation on the shared EUF egraph.
//
// Owned by EufSolver. Does NOT create a second congruence structure: select /
// store / const-array are interned as ordinary application nodes in the
// existing IncrementalEGraph (so array congruence is free). This class layers
// the four quantifier-free array axioms on top:
//
//   Row1  select(store(a,i,v),i) = v               (eager, no SAT split)
//   Const select(const(v),i)     = v               (eager, no SAT split)
//   Row2  i!=j => select(store(a,i,v),j)=select(a,j) (SAT lemma, full effort)
//   Ext   a!=b => select(a,k)!=select(b,k), fresh k  (SAT lemma, full effort)
//
// Termination: Row2/Ext never create store/const terms; Ext adds exactly one
// fresh index per array-disequality pair → finite saturation.
//
// All term-keyed state is monotonic (EufTermManager term ids are never reused
// and the manager is only cleared on reset()), so it does NOT need rollback;
// the eager Row1/Const merges are re-enqueued each check() if the egraph
// (which IS rolled back) does not already have them.
// ---------------------------------------------------------------------------
class ArrayReasoner {
public:
    ArrayReasoner();

    void setContext(EufTermManager* tm, IncrementalEGraph* egraph,
                    const CoreIr* ir, TheoryAtomRegistry* registry) {
        tm_ = tm;
        egraph_ = egraph;
        ir_ = ir;
        registry_ = registry;
    }

    // In Nelson-Oppen combination logics (QF_ALIA/ALRA/AUFLIA/AUFLRA) the
    // array index/element terms are arithmetic and shared with the arith
    // theory. Supplying the SharedTermRegistry lets Row2 build the (i=j)
    // antecedent as a SHARED-equality atom (observed by BOTH arith and EUF)
    // instead of an EUF-only equality, so an arith fact like (= i (+ j 0))
    // actually drives the Row2 case split. Null in pure QF_AX.
    void setSharedTermRegistry(const SharedTermRegistry* reg) { sharedTermRegistry_ = reg; }

    bool active() const { return tm_ != nullptr && egraph_ != nullptr; }

    void reset();

    // Scan all interned terms for array operations (select/store/const-array),
    // registering any newly discovered ones. Idempotent and monotonic. Returns
    // true if any new array term was discovered.
    bool discoverArrayTerms();

    // Enqueue any Row1/Const eager merges that the egraph does not already
    // reflect. Tautological, so safe to call on every check() (e.g. after a
    // backtrack that rolled back a previously-enqueued merge). Pushes into the
    // egraph's mergeQueue; the EufSolver saturation loop drains it.
    void enqueueEagerMerges(std::deque<PendingMerge>& outQueue);

    // Read-over-write completion. For each store term s and each read index idx
    // (an index appearing in some existing select), intern select(s, idx). This
    // makes a read index propagate THROUGH a store tower that is asserted EQUAL
    // to another array: lazy Row2 only peels a store when a select on it already
    // exists, so a positive array equality used as a HYPOTHESIS (e.g.
    // store(store(store S ...)...) = store(store(store S' ...)...)) leaves the
    // selects on the towers uninstantiated and the congruence that forces a read
    // value undischarged -> an actually-unsat formula escapes as a false SAT (the
    // QF_AX/QF_ALIA read2/read5 class). Creating select(s, idx) lets Row1/Row2 +
    // congruence decide it. Bounded by |stores| x |read-indices| (the index set
    // does not grow: created selects reuse existing read indices, and Row2 never
    // creates new stores), so saturation stays finite. Sound: only tautological
    // select terms are added, never new assertions.
    void completeStoreSelects(std::deque<PendingMerge>& outQueue);

    // #75 (XOLVER_AX_STORE_NOOP, default-ON; =0 to disable): store-store no-op merge. When two
    // stores of the SAME base with DISTINCT CONSTANT indices land in one e-graph
    // class (store(c,i,v) = store(c,j,w), i!=j), both writes are no-ops
    // (v=c[i], w=c[j]), so each store equals the base c. Eagerly merge store=base
    // at `mergeLevel` (= currentLevel_) so backtrack removes it; the merge reason
    // is ArrayRow2Cond with an EMPTY lit (i!=j is a constant tautology -> zero
    // literals) and argPairs={store1,store2} (the justification recurses on their
    // class membership). This lets UF congruence close an INDIRECT disequality
    // such as g(c)!=g(a) that the extensionality lemma never triggers between the
    // two arrays — the QF_AUFLRA a=store(c,0,v) ^ a=store(c,2,w) ^ g(c)!=g(a)
    // false-sat. Uses the proven Row2Cond merge path (vs the mkLemma path, which
    // did not drive the merge).
    void enqueueStoreNoopMerges(int mergeLevel, std::deque<PendingMerge>& outQueue);
    bool storeNoopEnabled() const { return storeNoopEnabled_; }

    // Produce one Row2 or Extensionality lemma if a fresh instance exists.
    // Returns the lemma literals (SAT polarity), or empty if none pending.
    // `disequalities` are the currently-active array-sort disequalities the
    // EUF solver knows about (lhs/rhs term ids).
    struct ArrayDiseq {
        EufTermId lhs;
        EufTermId rhs;
    };
    // `dedupOverride`: when non-null, use this set for Row2 (store,j)-pair dedup
    // instead of the internal row2Done_. The L13 Standard-effort split passes its
    // OWN set so it does not mark row2Done_ and starve the Full-effort path
    // (the ax_007 regression). Default null = original behavior (uses row2Done_).
    std::optional<std::vector<SatLit>>
    instantiateLemma(const std::vector<ArrayDiseq>& disequalities,
                     std::unordered_set<uint64_t>* dedupOverride = nullptr);

    // Collect the SharedTermIds of all array INDEX terms (the index arg of every
    // select/store). Used by the combination layer to scope deduced-equality
    // propagation to array-index pairs (so an entailed index equality reaches a
    // pending Row1/Row2 without flooding the SAT core with every deduced equality).
    void collectIndexSharedTerms(std::unordered_set<SharedTermId>& out) const;

    // Collect the SharedTermIds of array VALUE/element terms (stored value arg[2]
    // of every store + each arith-shared read result). Used by TheoryManager to
    // defer value-pair deduced equalities to Full effort — the same Standard-effort
    // cache-poisoning fix already applied to index pairs (alra_010 value side).
    void collectValueSharedTerms(std::unordered_set<SharedTermId>& out) const;

    // Accessors for model construction.
    const std::vector<EufTermId>& selectTerms() const { return selectTerms_; }
    const std::vector<EufTermId>& storeTerms() const { return storeTerms_; }
    const std::vector<EufTermId>& constArrayTerms() const { return constArrayTerms_; }

    bool isSelect(EufTermId t) const { return selectSet_.count(t) != 0; }
    bool isStore(EufTermId t) const { return storeSet_.count(t) != 0; }
    bool isConstArray(EufTermId t) const { return constArraySet_.count(t) != 0; }

private:
    EufTermManager* tm_ = nullptr;
    IncrementalEGraph* egraph_ = nullptr;
    const CoreIr* ir_ = nullptr;
    TheoryAtomRegistry* registry_ = nullptr;
    const SharedTermRegistry* sharedTermRegistry_ = nullptr;

    // Build the Row2 index-equality literal (i=j). If both index exprs are
    // registered shared arith terms, route through the shared-equality
    // mechanism (observed by arith AND EUF); otherwise fall back to an
    // EUF-only equality atom (pure QF_AX with uninterpreted indices).
    SatLit makeRow2IndexEqLit(ExprId iExpr, ExprId jExpr);

    // Reserved array symbol names (mirror EufTermManager::builtinName).
    bool symIsSelect(EufTermId t) const;
    bool symIsStore(EufTermId t) const;
    bool symIsConstArray(EufTermId t) const;

    // XOLVER_AX_ROW2_CONST: eagerly apply Row2 (no SAT split) when the write
    // and read indices are syntactically-distinct numeric/bool constants. Read
    // once at construction.
    bool row2ConstEnabled_ = false;

    // XOLVER_AX_LAZY (default-OFF, L1): RELEVANCY-DRIVEN read-over-write
    // completion. The default eager path interns select(arr,idx) for the full
    // arrays×read-indices cross-product (24k+ selects on the cs_* concurrency
    // traces vs z3's ~100 axiom instantiations — a primary TO cause). The lazy
    // path instead seeds select(s,idx) ONLY for stores s in the SAME e-graph
    // class as an array actually read at idx — the towers a read genuinely needs
    // to peel. Row2 then chains the peeling. Verdict-sound (completion adds only
    // tautological selects; restricting which we add is completeness-only, floored
    // by arrayModelDefinitelyViolates). Read once at construction.
    bool lazyComplete_ = false;
    void completeStoreSelectsLazy(std::deque<PendingMerge>& outQueue);

public:
    // L2 (XOLVER_AX_ROW2_DISEQ): the disequality descriptor the eager Row2-cond
    // pass needs — the matched diseq endpoints (rep(dForI)==rep(i),
    // rep(dForJ)==rep(j)) and the disequality's reason literal.
    struct Row2CondDiseq {
        EufTermId dForI;
        EufTermId dForJ;
        SatLit reason;
    };
    // Eager Row2 MERGE for KNOWN-disequal index pairs (L2). For every read
    // select(arr,j) with a store(a,i,v) in arr's class where queryDiseq(i,j)
    // reports i≠j known, merge select(store(a,i,v),j) = select(a,j) with an
    // ArrayRow2Cond reason (diseq literal + chains i~dForI, j~dForJ). Dedup is
    // implicit (skip when the two reads are already same-class), so it is
    // backtrack-correct: a removed merge is simply re-derived. mergeLevel is
    // stamped on each merge (pass currentLevel_ — conservative, never stale).
    void enqueueRow2CondMerges(
        const std::function<std::optional<Row2CondDiseq>(EufTermId, EufTermId)>& queryDiseq,
        int mergeLevel,
        std::deque<PendingMerge>& outQueue);
    bool row2DiseqEnabled() const { return row2DiseqEnabled_; }
private:
    bool row2DiseqEnabled_ = false;
    bool storeNoopEnabled_ = false;  // #75 store-store no-op merge (set default-ON in ctor)

    // Read-over-write completion (see completeStoreSelects). Default ON: needed
    // for QF_AX/QF_ALIA soundness (read2/read5 false-SAT). XOLVER_AX_NO_SELECT_COMPLETE
    // disables it (A/B baseline only). Read once at construction.
    bool selectCompletionEnabled_ = true;
    // Dedup of (store-term-id, read-index-term-id) pairs already completed.
    std::unordered_set<uint64_t> selectCompleteDone_;
    // XOLVER_AX_COMPLETE_BUDGET: cap on total completion selects interned over
    // the whole solve (0 = unbounded). Once reached, completeStoreSelects is a
    // no-op. Verdict-sound (arrayModelDefinitelyViolates floors any missed
    // instance); bounds the driver-family O(arrays×indices) blowup.
    size_t completeBudget_ = 0;
    size_t completeInternsDone_ = 0;
    // Origin ExprIds of FRESH extensionality witness indices. These must be
    // EXCLUDED from the completion read-index set: Ext mints one per array
    // disequality pair, so treating them as read indices would (a) grow the
    // index set unboundedly and (b) fan a witness across every store for no
    // reason (Ext already builds the two witness selects it needs). Completion
    // is for POSITIVE array equalities; Ext owns the disequality side.
    std::unordered_set<ExprId> extWitnessIdx_;
    // Default-ON (PROMOTED 2026-05-31; opt-out XOLVER_AX_NO_EXT_WITNESS_COMPLETE):
    // also fan the fresh extensionality witness index k through the store towers
    // in completeStoreSelects. Needed for the storeinv class — a positive
    // store-equality hypothesis (store-tower = store-tower) combined with an
    // array disequality a!=b is only refuted when the witness k from Ext is read
    // THROUGH the towers (Row2 peels to select(a,k)/select(b,k), congruence on
    // the equal towers contradicts the Ext disequality). Earlier the default
    // excluded witnesses (extWitnessIdx_) out of a concern it would destabilise
    // storecomm genuine-sats; Phase A verified that concern does NOT reproduce
    // (storecomm stable, reg 668/668), so witnesses are re-admitted by default
    // via the dedicated witness-term list below (bounded: one witness per
    // array-disequality pair, each read across the finite array set).
    bool extWitnessComplete_ = true;
    // EufTermIds of the fresh Ext witness index terms (the k in select(a,k)).
    // Populated by instantiateLemma when minting a witness; consumed by
    // completeStoreSelects under extWitnessComplete_ to seed the read-index set
    // (extWitnessIdx_ holds the ExprId origins for the skip path; this holds the
    // interned index term ids needed by completion's EufTermId-keyed readIdx).
    std::vector<EufTermId> extWitnessIdxTerms_;
    // Select terms created INTERNALLY by internSelect (Row1/Row2/Ext/completion),
    // as opposed to the ORIGINAL formula selects interned by the EUF term path.
    // The completion read-index set must be seeded only from ORIGINAL selects:
    // Row1 synthesizes select(store, store-index) for every write index, so
    // seeding from internal selects would fan completion across the (irrelevant)
    // store-index set and blow up genuine sats (storecomm). The genuine reads are
    // exactly the formula's own select indices.
    std::unordered_set<EufTermId> internalSelect_;

    // Incremental completeStoreSelects state (perf, QF_ANIA budget). Avoid
    // re-iterating the O(arrays x indices) cross-product on every cb_check
    // call: each call only processes pairs that involve a NEW array or a NEW
    // read-index since the last call. termManager_ + selectTerms_ are monotonic
    // (never shrink across backtracks), and selectCompleteDone_ is already
    // persistent across backtracks in the existing code, so the incremental
    // pass is strictly equivalent to the original full-sweep + dedup-skip
    // behavior — just without paying the O(N*M) hash lookups every call.
    size_t completeLastSelectScanEnd_ = 0;
    EufTermId completeLastTermScanEnd_ = 0;
    std::vector<EufTermId> completeArrayCache_;
    std::vector<EufTermId> completeReadIdxCache_;
    std::unordered_set<EufTermId> completeReadIdxSeen_;

    // A canonical token for t IF its origin is a numeric or boolean constant
    // literal (so distinct tokens ⇒ distinct values). Returns nullopt for
    // uninterpreted-sort constants (distinct names do NOT imply distinct
    // values) and non-constants. Used to prove i != j without a SAT literal.
    std::optional<std::string> constToken(EufTermId t) const;
    bool provablyDistinctConstIndices(EufTermId i, EufTermId j) const;

    // Registered array terms (monotonic, never rolled back).
    std::vector<EufTermId> selectTerms_;
    std::vector<EufTermId> storeTerms_;
    std::vector<EufTermId> constArrayTerms_;
    std::unordered_set<EufTermId> selectSet_;
    std::unordered_set<EufTermId> storeSet_;
    std::unordered_set<EufTermId> constArraySet_;
    EufTermId nextTermToScan_ = 0;

    // Intern (or reuse) a CoreIr Select node select(array, index) and return
    // its EufTermId, registering it with the egraph. Used by Row2/Ext to build
    // the read terms that appear in the lemma. May add a CoreExpr to ir_.
    EufTermId internSelect(ExprId arrayExpr, ExprId indexExpr,
                           std::deque<PendingMerge>& outQueue);

    // ExprId of a term given its EufTermId origin (or NullExpr).
    ExprId originExpr(EufTermId t) const;

    // Lemma dedup, keyed by STABLE term ids (never eclass reps). For Row2 the
    // key is (store-term-id, read-index-term-id). For Ext the key is the
    // canonical ordered (array-term-id, array-term-id) pair PLUS the source
    // disequality is enforced once by also recording the pair.
    std::unordered_set<uint64_t> row2Done_;
    std::unordered_set<uint64_t> extDone_;

    static uint64_t pairKey(uint32_t a, uint32_t b) {
        return (static_cast<uint64_t>(a) << 32) | static_cast<uint64_t>(b);
    }
};

} // namespace xolver
