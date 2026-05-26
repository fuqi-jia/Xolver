#pragma once
#include "theory/euf/EufTypes.h"
#include <vector>
#include <cstdint>

namespace zolver {

class ProofForest {
public:
    ProofForest();

    void addEdge(EufTermId u, EufTermId v, const MergeReason& reason);
    size_t snapshot() const;
    void rollback(size_t snap);
    void clear();

    // Returns edge IDs along the path u→v in the active forest.
    // Empty if no path (should not happen for same-class terms).
    std::vector<size_t> path(EufTermId u, EufTermId v) const;

    size_t activeEdgeCount() const { return activeEdgeCount_; }

    const MergeReason& edgeReason(size_t edgeId) const { return edges_[edgeId].reason; }

private:
    struct Edge {
        EufTermId u;
        EufTermId v;
        MergeReason reason;
    };
    std::vector<Edge> edges_;
    std::vector<std::vector<std::pair<EufTermId, size_t>>> adj_;
    size_t activeEdgeCount_ = 0;

    // ZOLVER_UF_FAST_CC: O(k) rollback (pop trailing edges) instead of an
    // O(k·degree) remove_if scan. Sound because edges are appended in
    // increasing id and rolled back LIFO, so removed edges sit at each
    // adjacency list's tail. Read once at construction.
    bool fastRollback_ = false;
};

} // namespace zolver
