#include "theory/euf/ProofForest.h"
#include <algorithm>
#include <queue>
#include <unordered_map>

namespace nlcolver {

void ProofForest::addEdge(EufTermId u, EufTermId v, const MergeReason& reason) {
    size_t edgeId = edges_.size();
    edges_.push_back({u, v, reason});

    if (u >= adj_.size()) adj_.resize(u + 1);
    if (v >= adj_.size()) adj_.resize(v + 1);

    adj_[u].push_back({v, edgeId});
    adj_[v].push_back({u, edgeId});

    activeEdgeCount_ = edges_.size();
}

size_t ProofForest::snapshot() const {
    return activeEdgeCount_;
}

void ProofForest::rollback(size_t snap) {
    // Remove edges with edgeId >= snap from adjacency lists.
    for (size_t eid = snap; eid < edges_.size(); ++eid) {
        const auto& e = edges_[eid];
        if (e.u < adj_.size()) {
            auto& au = adj_[e.u];
            au.erase(std::remove_if(au.begin(), au.end(),
                [eid](const auto& p){ return p.second == eid; }), au.end());
        }
        if (e.v < adj_.size()) {
            auto& av = adj_[e.v];
            av.erase(std::remove_if(av.begin(), av.end(),
                [eid](const auto& p){ return p.second == eid; }), av.end());
        }
    }
    edges_.resize(snap);
    activeEdgeCount_ = snap;
}

void ProofForest::clear() {
    edges_.clear();
    adj_.clear();
    activeEdgeCount_ = 0;
}

std::vector<size_t> ProofForest::path(EufTermId u, EufTermId v) const {
    if (u == v) return {};
    if (u >= adj_.size() || v >= adj_.size()) return {};

    std::queue<EufTermId> q;
    std::unordered_map<EufTermId, EufTermId> parentTerm;
    std::unordered_map<EufTermId, size_t> parentEdge;

    q.push(u);
    parentTerm[u] = u;

    while (!q.empty()) {
        EufTermId cur = q.front();
        q.pop();

        if (cur >= adj_.size()) continue;
        for (const auto& [next, edgeId] : adj_[cur]) {
            if (edgeId >= activeEdgeCount_) continue;
            if (parentTerm.count(next)) continue;

            parentTerm[next] = cur;
            parentEdge[next] = edgeId;

            if (next == v) {
                std::vector<size_t> result;
                EufTermId node = v;
                while (node != u) {
                    result.push_back(parentEdge[node]);
                    node = parentTerm[node];
                }
                std::reverse(result.begin(), result.end());
                return result;
            }
            q.push(next);
        }
    }
    return {};
}

} // namespace nlcolver
