#pragma once
#include "theory/euf/EufTypes.h"
#include <vector>
#include <cstdint>

namespace xolver {

// ---------------------------------------------------------------------------
// ProofForest — Nieuwenhuis-Oliveras proof-producing congruence forest.
//
// Each term node has at most one parent (a true FOREST, never a general graph),
// with the edge labelled by the MergeReason that justified node == parent. A
// merge of two DISTINCT classes calls addEdge(u,v,r): we first re-root u's tree
// (reverse the u→root chain so u becomes a root) and then point u at v. This
// keeps the structure a forest in which the path between any two same-tree nodes
// is UNIQUE, so explaining a==b = collecting the edge labels along a→NCA→b is a
// sound, complete derivation. (The previous implementation stored bidirectional
// edges in a general graph and used BFS, which is not a sound proof producer —
// it could return an explanation that did not entail the equality, yielding
// false UNSAT. See the QG-classification differential.)
//
// Rollback is a trail of parent-pointer changes (the part that bites): snapshot
// records trail length; rollback undoes parent/label changes in LIFO order,
// restoring the forest exactly. Label storage is an append-only pool; entries
// whose edges are rolled back simply become unreferenced (never read).
// ---------------------------------------------------------------------------
class ProofForest {
public:
    // addEdge is only ever called to merge two DISTINCT classes (the caller
    // checks union-find first), so u and v are always in different trees here.
    void addEdge(EufTermId u, EufTermId v, const MergeReason& reason);
    // Level-tagged variant: every parent change pushed during this addEdge is
    // tagged with `level`, enabling a level-FILTER rollback that complements
    // the standard count-based rollback (see rollbackByLevel below).
    void addEdgeAtLevel(EufTermId u, EufTermId v, const MergeReason& reason, int level);

    size_t snapshot() const { return trail_.size(); }
    void rollback(size_t snap);
    // Level-FILTER rollback: pop trail entries from the end as long as the top
    // entry has level > targetLevel. Together with the count-based rollback
    // this catches "out-of-monotonic-order" entries that the count-based
    // truncation alone would leave behind (combination interface (dis)equality
    // can append a low-level merge after a high-level boundary was already
    // recorded — count-based truncation drops level=high merges but keeps the
    // level=low one whose dependency was rolled back). Idempotent and safe to
    // call after rollback(snap).
    void rollbackByLevel(int targetLevel);
    void clear();

    // Label indices along the unique tree path u → NCA → v. Empty if u == v or
    // u and v are in different trees (the latter must not happen for terms the
    // union-find reports as same-class).
    std::vector<size_t> path(EufTermId u, EufTermId v) const;

    const MergeReason& edgeReason(size_t labelIdx) const { return labels_[labelIdx]; }

    // Accessors (also used by unit tests). A root satisfies parentOf(t) == t.
    EufTermId parentOf(EufTermId t) const { return t < parent_.size() ? parent_[t] : t; }
    size_t labelIdxOf(EufTermId t) const { return t < edgeLabelIdx_.size() ? edgeLabelIdx_[t] : 0; }
    size_t nodeCount() const { return parent_.size(); }

private:
    std::vector<EufTermId> parent_;     // parent_[t]; t is a root iff parent_[t]==t
    std::vector<size_t> edgeLabelIdx_;  // label of the edge t → parent_[t]
    std::vector<MergeReason> labels_;   // append-only reason pool

    struct ParentChange {
        EufTermId node;
        EufTermId oldParent;
        size_t oldLabelIdx;
        // Level at which the parent change was made. Used by rollbackByLevel
        // to drop trail entries whose creating merge was at level > target,
        // catching out-of-monotonic-order merges that count-based rollback
        // alone leaves stale. 0 = pre-fix (level-0 / unknown) is safe default.
        int level = 0;
    };
    std::vector<ParentChange> trail_;

    void ensureNode(EufTermId t);
    void setParent(EufTermId node, EufTermId newParent, size_t newLabelIdx);
    // currentLevel_ is captured into ParentChange.level at every setParent.
    // addEdgeAtLevel sets it before reorienting; addEdge legacy keeps it 0.
    int currentLevel_ = 0;
    void makeRoot(EufTermId u);
};

} // namespace xolver
