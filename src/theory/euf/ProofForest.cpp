#include "theory/euf/ProofForest.h"
#include <unordered_set>

namespace xolver {

void ProofForest::clear() {
    parent_.clear();
    edgeLabelIdx_.clear();
    labels_.clear();
    trail_.clear();
}

void ProofForest::ensureNode(EufTermId t) {
    if (t >= parent_.size()) {
        size_t old = parent_.size();
        parent_.resize(t + 1);
        edgeLabelIdx_.resize(t + 1, 0);
        for (size_t i = old; i <= t; ++i) {
            parent_[i] = static_cast<EufTermId>(i);  // each new node is its own root
        }
    }
}

void ProofForest::setParent(EufTermId node, EufTermId newParent, size_t newLabelIdx) {
    trail_.push_back({node, parent_[node], edgeLabelIdx_[node]});
    parent_[node] = newParent;
    edgeLabelIdx_[node] = newLabelIdx;
}

void ProofForest::makeRoot(EufTermId u) {
    // Reverse the chain u → p1 → p2 → ... → root so that u becomes the root,
    // carrying each edge's label with the edge as its direction flips.
    EufTermId p1 = parent_[u];
    size_t lUp1 = edgeLabelIdx_[u];   // label of edge u ↔ p1
    setParent(u, u, 0);               // u is now a root
    if (p1 == u) return;              // u was already a root: nothing to reverse

    EufTermId cur = p1;
    size_t edgeLabel = lUp1;          // label of the edge between cur and its (new) child
    EufTermId newParent = u;
    while (true) {
        EufTermId curOldParent = parent_[cur];
        size_t curOldLabel = edgeLabelIdx_[cur];
        bool curIsRoot = (curOldParent == cur);
        setParent(cur, newParent, edgeLabel);  // cur now points back toward u
        if (curIsRoot) break;
        newParent = cur;
        edgeLabel = curOldLabel;
        cur = curOldParent;
    }
}

void ProofForest::addEdge(EufTermId u, EufTermId v, const MergeReason& reason) {
    ensureNode(u);
    ensureNode(v);
    size_t labelIdx = labels_.size();
    labels_.push_back(reason);
    makeRoot(u);                     // u becomes the root of its tree
    setParent(u, v, labelIdx);       // attach u (and its reoriented tree) under v
}

void ProofForest::rollback(size_t snap) {
    while (trail_.size() > snap) {
        ParentChange c = trail_.back();
        trail_.pop_back();
        parent_[c.node] = c.oldParent;
        edgeLabelIdx_[c.node] = c.oldLabelIdx;
    }
    // labels_ is append-only: entries added after `snap` are now unreferenced
    // (their edges were rolled back) and are never read again.
}

std::vector<size_t> ProofForest::path(EufTermId u, EufTermId v) const {
    if (u == v) return {};
    if (u >= parent_.size() || v >= parent_.size()) return {};

    // Ancestors of u (u up to its root).
    std::unordered_set<EufTermId> uAnc;
    for (EufTermId c = u;;) {
        uAnc.insert(c);
        EufTermId p = parent_[c];
        if (p == c) break;
        c = p;
    }

    // Walk v up to the nearest common ancestor.
    EufTermId nca = NullEufTerm;
    for (EufTermId c = v;;) {
        if (uAnc.count(c)) { nca = c; break; }
        EufTermId p = parent_[c];
        if (p == c) break;
        c = p;
    }
    if (nca == NullEufTerm) return {};  // different trees

    std::vector<size_t> out;
    for (EufTermId c = u; c != nca; c = parent_[c]) out.push_back(edgeLabelIdx_[c]);
    for (EufTermId c = v; c != nca; c = parent_[c]) out.push_back(edgeLabelIdx_[c]);
    return out;
}

} // namespace xolver
