#pragma once
#include <vector>
#include <optional>
#include <cstddef>
#include <cstdint>
#include <cassert>
#include <algorithm>
#include <unordered_map>
#include <unordered_set>
#include <queue>

namespace xolver {

/**
 * Rollback union-find with sound per-edge explanations.
 *
 * `find`/`same`/`unite` use union-by-size for efficiency. Explanations are
 * produced from a SEPARATE proof forest: each `unite(a, b, r)` records an
 * undirected edge between the ACTUAL asserted terms a and b labeled r. Because
 * a unite only ever connects two distinct classes, the proof graph is a forest,
 * so the path between any two same-class nodes is unique; `explain(a, b)` walks
 * that path and returns its edge labels.
 *
 * Storing reasons on the union-by-size *root* edge (the previous design) was
 * unsound: the reason justifies the asserted pair (a, b), but the size-tree
 * edge connects the two class roots, which are generally NOT a and b — so the
 * collected reasons did not form a valid equality chain and `explain` returned
 * an incomplete set, producing unsound interface-disequality conflicts
 * (e.g. QF_UFLIA hash_sat_03_08 false UNSAT).
 *
 * @tparam Reason Type stored on each merge edge (e.g. SatLit).
 */
template <typename Reason>
class ExplainableRollbackUnionFind {
public:
    using Id = uint32_t;

    ExplainableRollbackUnionFind() = default;
    explicit ExplainableRollbackUnionFind(size_t n) {
        parent_.reserve(n);
        size_.reserve(n);
        proofAdj_.reserve(n);
        for (size_t i = 0; i < n; ++i) addNode();
    }

    Id addNode() {
        Id id = static_cast<Id>(parent_.size());
        parent_.push_back(id);
        size_.push_back(1);
        proofAdj_.push_back({});
        return id;
    }

    Id find(Id x) const {
        assert(x < parent_.size());
        while (parent_[x] != x) {
            x = parent_[x];
        }
        return x;
    }

    bool same(Id a, Id b) const {
        if (a >= parent_.size() || b >= parent_.size()) return false;
        return find(a) == find(b);
    }

    struct UniteResult {
        bool merged;
        Id winner;
        Id loser;
    };

    UniteResult unite(Id a, Id b, const Reason& reason) {
        Id ra = find(a);
        Id rb = find(b);

        if (ra == rb) {
            return {false, ra, rb};
        }

        // union-by-size: larger becomes winner (parent)
        if (size_[ra] < size_[rb]) {
            std::swap(ra, rb);
        }

        changes_.push_back(Change{rb, ra, size_[ra], a, b});

        parent_[rb] = ra;
        size_[ra] += size_[rb];

        // Proof forest: undirected edge between the ACTUAL asserted terms.
        proofAdj_[a].push_back({b, reason});
        proofAdj_[b].push_back({a, reason});

        return {true, ra, rb};
    }

    /**
     * Return the reasons along the proof-forest path connecting a and b.
     * Precondition: same(a, b) must be true.
     */
    std::vector<Reason> explain(Id a, Id b) const {
        assert(same(a, b));
        if (a == b) return {};

        // BFS over the proof forest from a to b.
        std::unordered_map<Id, Id> prevNode;       // node -> predecessor on path
        std::unordered_map<Id, Reason> prevReason; // node -> reason of edge to predecessor
        std::unordered_set<Id> visited;
        std::queue<Id> q;
        q.push(a);
        visited.insert(a);

        bool found = false;
        while (!q.empty() && !found) {
            Id cur = q.front();
            q.pop();
            for (const auto& [nxt, reason] : proofAdj_[cur]) {
                if (visited.count(nxt)) continue;
                visited.insert(nxt);
                prevNode[nxt] = cur;
                prevReason.emplace(nxt, reason);
                if (nxt == b) { found = true; break; }
                q.push(nxt);
            }
        }

        std::vector<Reason> reasons;
        if (!found) return reasons; // should not happen when same(a,b)

        Id cur = b;
        while (cur != a) {
            reasons.push_back(prevReason.at(cur));
            cur = prevNode.at(cur);
        }
        return reasons;
    }

    using Snapshot = size_t;

    Snapshot snapshot() const {
        return changes_.size();
    }

    void rollback(Snapshot snap) {
        while (changes_.size() > snap) {
            auto ch = changes_.back();
            changes_.pop_back();
            parent_[ch.childRoot] = ch.childRoot;
            size_[ch.parentRoot] = ch.oldParentSize;
            // Remove this unite's proof edge (LIFO: it is the last entry on
            // both endpoints' adjacency lists).
            if (!proofAdj_[ch.termA].empty()) proofAdj_[ch.termA].pop_back();
            if (!proofAdj_[ch.termB].empty()) proofAdj_[ch.termB].pop_back();
        }
    }

    uint32_t classSize(Id root) const {
        Id r = find(root);
        return size_[r];
    }

    size_t size() const { return parent_.size(); }

private:
    std::vector<Id> parent_;
    std::vector<uint32_t> size_;
    std::vector<std::vector<std::pair<Id, Reason>>> proofAdj_;

    struct Change {
        Id childRoot;
        Id parentRoot;
        uint32_t oldParentSize;
        Id termA;  // actual asserted terms for the proof edge
        Id termB;
    };
    std::vector<Change> changes_;
};

} // namespace xolver
