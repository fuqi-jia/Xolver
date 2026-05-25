#pragma once

#include "expr/types.h"
#include "theory/euf/EufTypes.h"
#include "theory/core/TheoryAtomTypes.h"
#include <vector>
#include <deque>
#include <unordered_set>
#include <unordered_map>
#include <optional>
#include <cstdint>

namespace nlcolver {

class EufTermManager;
class IncrementalEGraph;
class CoreIr;
class TheoryAtomRegistry;
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
    void setContext(EufTermManager* tm, IncrementalEGraph* egraph,
                    const CoreIr* ir, TheoryAtomRegistry* registry) {
        tm_ = tm;
        egraph_ = egraph;
        ir_ = ir;
        registry_ = registry;
    }

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

    // Produce one Row2 or Extensionality lemma if a fresh instance exists.
    // Returns the lemma literals (SAT polarity), or empty if none pending.
    // `disequalities` are the currently-active array-sort disequalities the
    // EUF solver knows about (lhs/rhs term ids).
    struct ArrayDiseq {
        EufTermId lhs;
        EufTermId rhs;
    };
    std::optional<std::vector<SatLit>>
    instantiateLemma(const std::vector<ArrayDiseq>& disequalities);

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

    // Reserved array symbol names (mirror EufTermManager::builtinName).
    bool symIsSelect(EufTermId t) const;
    bool symIsStore(EufTermId t) const;
    bool symIsConstArray(EufTermId t) const;

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

} // namespace nlcolver
