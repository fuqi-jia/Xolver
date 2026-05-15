#pragma once
#include <vector>
#include <optional>
#include <cstddef>
#include <cstdint>
#include <cassert>
#include <algorithm>
#include <unordered_map>

namespace nlcolver {

/**
 * RollbackUnionFind with per-edge explanation reasons.
 * No path compression (to preserve explanation forest).
 * Union by size is used.
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
        edgeReason_.reserve(n);
        for (size_t i = 0; i < n; ++i) addNode();
    }

    Id addNode() {
        Id id = static_cast<Id>(parent_.size());
        parent_.push_back(id);
        size_.push_back(1);
        edgeReason_.push_back(std::nullopt);
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

        changes_.push_back(Change{
            rb,           // childRoot
            ra,           // parentRoot
            size_[ra],    // oldParentSize
            edgeReason_[rb] // oldEdgeReason
        });

        parent_[rb] = ra;
        size_[ra] += size_[rb];
        edgeReason_[rb] = reason;

        return {true, ra, rb};
    }

    /**
     * Return the reasons along the UF tree path that connects a and b.
     * Precondition: same(a, b) must be true.
     */
    std::vector<Reason> explain(Id a, Id b) const {
        assert(same(a, b));

        std::vector<Reason> reasons;

        // Find path from a to root, record position of each node
        std::unordered_map<Id, size_t> posA;
        std::vector<Id> pathA;
        Id cur = a;
        while (true) {
            posA[cur] = pathA.size();
            pathA.push_back(cur);
            if (parent_[cur] == cur) break;
            cur = parent_[cur];
        }

        // Walk from b to root, find first common node (LCA)
        Id lca = static_cast<Id>(-1);
        cur = b;
        while (true) {
            auto it = posA.find(cur);
            if (it != posA.end()) {
                lca = cur;
                break;
            }
            if (parent_[cur] == cur) break;
            cur = parent_[cur];
        }

        assert(lca != static_cast<Id>(-1));

        // Collect reasons from a up to (but not including) lca
        cur = a;
        while (cur != lca) {
            assert(edgeReason_[cur].has_value());
            reasons.push_back(*edgeReason_[cur]);
            cur = parent_[cur];
        }

        // Collect reasons from b up to (but not including) lca
        cur = b;
        while (cur != lca) {
            assert(edgeReason_[cur].has_value());
            reasons.push_back(*edgeReason_[cur]);
            cur = parent_[cur];
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
            edgeReason_[ch.childRoot] = ch.oldEdgeReason;
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
    std::vector<std::optional<Reason>> edgeReason_;

    struct Change {
        Id childRoot;
        Id parentRoot;
        uint32_t oldParentSize;
        std::optional<Reason> oldEdgeReason;
    };
    std::vector<Change> changes_;
};

} // namespace nlcolver
