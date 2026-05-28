#pragma once

#include "theory/arith/dl/DlWeight.h"
#include "expr/types.h"
#include "sat/SatSolver.h"
#include <vector>
#include <string>
#include <unordered_map>

namespace xolver {

using EdgeId = size_t;

// ============================================================================
// Edge in a difference constraint graph.
// Edge y -> x with weight w means: value(x) <= value(y) + w.
// ============================================================================
template <typename Weight>
struct DlEdge {
    int from;         // y
    int to;           // x
    Weight weight;    // upper bound
    SatLit reason;    // active literal causing this edge
    EdgeId id;
};

// ============================================================================
// Sparse difference constraint graph.
// Node 0 is always the special ZERO variable.
// ============================================================================
template <typename Weight>
class DifferenceGraph {
public:
    DifferenceGraph() {
        // Node 0 is ZERO
        nodeToName_.push_back("__ZERO__");
        nameToNode_["__ZERO__"] = 0;
    }

    int getOrCreateNode(const std::string& name) {
        auto it = nameToNode_.find(name);
        if (it != nameToNode_.end()) return it->second;
        int id = static_cast<int>(nodeToName_.size());
        nodeToName_.push_back(name);
        nameToNode_[name] = id;
        outgoing_.emplace_back();
        return id;
    }

    int zeroNode() const { return 0; }

    int nodeByName(const std::string& name) const {
        auto it = nameToNode_.find(name);
        if (it != nameToNode_.end()) return it->second;
        return -1;
    }

    const std::string& nodeName(int node) const {
        static const std::string empty;
        if (node >= 0 && node < static_cast<int>(nodeToName_.size()))
            return nodeToName_[node];
        return empty;
    }

    EdgeId addEdge(int from, int to, const Weight& w, SatLit reason) {
        EdgeId id = edges_.size();
        edges_.push_back(DlEdge<Weight>{from, to, w, reason, id});
        // Ensure outgoing vector is large enough
        if (from >= static_cast<int>(outgoing_.size())) {
            outgoing_.resize(from + 1);
        }
        outgoing_[from].push_back(id);
        return id;
    }

    void clear() {
        edges_.clear();
        outgoing_.clear();
        outgoing_.resize(1); // node 0 always exists
        // Keep node mappings
    }

    int numNodes() const {
        return static_cast<int>(nodeToName_.size());
    }

    const std::vector<DlEdge<Weight>>& edges() const { return edges_; }
    const std::vector<std::vector<EdgeId>>& outgoing() const { return outgoing_; }
    const DlEdge<Weight>& edge(EdgeId id) const { return edges_[id]; }

private:
    std::vector<std::string> nodeToName_;
    std::unordered_map<std::string, int> nameToNode_;
    std::vector<DlEdge<Weight>> edges_;
    std::vector<std::vector<EdgeId>> outgoing_;
};

} // namespace xolver
