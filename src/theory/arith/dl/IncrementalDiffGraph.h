#pragma once

#include "theory/arith/dl/DifferenceGraph.h"
#include "theory/arith/dl/BellmanFord.h"
#include <vector>
#include <algorithm>

namespace zolver {

// ============================================================================
// IncrementalDiffGraph: stateful difference-constraint graph that maintains a
// feasible potential `pot_` across asserts/backtracks, so the expensive full
// Bellman-Ford runs only when a newly-enabled edge actually conflicts with the
// current potential — not on every check.
//
// Edge from->to weight w means value(to) <= value(from) + w. `pot_` is feasible
// iff for every enabled edge: pot_[to] - pot_[from] <= w (slack >= 0).
// model read-off: value(v) = pot_[v] - pot_[zero].
//
// enableEdge(from,to,w):
//   - slack(new edge) >= 0 under pot_  => already feasible, O(1), pot_ kept.
//   - else run full Bellman-Ford ONCE over all enabled edges:
//       * negative cycle  => INFEASIBLE; the edge stays recorded so the caller
//                            can read `lastCycle()` (the proven extractor's exact
//                            cycle) for the conflict.
//       * feasible        => adopt the new feasible potential (bf.dist).
// backtrack(level): pop edges enabled above `level`. Removing constraints can
//   never make a feasible assignment infeasible, so pot_ stays valid with no
//   recompute.
//
// Soundness: feasibility verdict + the negative cycle both come from the proven
// full Bellman-Ford; pot_ is only ever set to a BF-certified feasible
// assignment (or kept across a slack>=0 add / an edge removal). Template over
// Weight so IDL (mpz_class) and RDL (RdlWeight) share one implementation.
// ============================================================================
template <typename Weight>
class IncrementalDiffGraph {
public:
    IncrementalDiffGraph() {
        nodeToName_.push_back("__ZERO__");
        nameToNode_["__ZERO__"] = 0;
        pot_.emplace_back();  // ZERO potential = 0
    }

    int getOrCreateNode(const std::string& name) {
        auto it = nameToNode_.find(name);
        if (it != nameToNode_.end()) return it->second;
        int id = static_cast<int>(nodeToName_.size());
        nodeToName_.push_back(name);
        nameToNode_[name] = id;
        pot_.emplace_back();  // new isolated node, potential 0 (feasible)
        return id;
    }

    int zeroNode() const { return 0; }
    int numNodes() const { return static_cast<int>(nodeToName_.size()); }
    const std::string& nodeName(int n) const { return nodeToName_[n]; }
    int nodeByName(const std::string& name) const {
        auto it = nameToNode_.find(name);
        return it != nameToNode_.end() ? it->second : -1;
    }
    const Weight& potential(int n) const { return pot_[n]; }
    const std::vector<EdgeId>& lastCycle() const { return lastCycle_; }
    size_t numEnabledEdges() const { return edges_.size(); }
    const DlEdge<Weight>& edge(EdgeId id) const { return edges_[id]; }

    // Add edge from->to (weight w) at `level`. Returns true if the graph stays
    // feasible (pot_ valid), false on a negative cycle (lastCycle() holds it).
    bool enableEdge(int from, int to, const Weight& w, SatLit reason, int level) {
        EdgeId id = edges_.size();
        edges_.push_back(DlEdge<Weight>{from, to, w, reason, id});
        edgeLevel_.push_back(level);

        // Already satisfied by the current feasible potential? O(1), no BF.
        // slack >= 0  <=>  pot_[to] - pot_[from] <= w  <=>  NOT (... > w).
        if (!((pot_[to] - pot_[from]) > w)) {
            return true;
        }

        // The new edge violates pot_. Re-solve from scratch (proven full BF).
        BfResult<Weight> bf = runFullOnEnabled();
        if (bf.negativeCycle) {
            lastCycle_ = std::move(bf.cycle);
            return false;
        }
        pot_ = std::move(bf.dist);   // adopt the new BF-certified feasible potential
        lastCycle_.clear();
        return true;
    }

    // Undo every enable recorded with level > `level`. pot_ remains feasible
    // (removing constraints preserves feasibility), so it is NOT recomputed.
    void backtrack(int level) {
        while (!edgeLevel_.empty() && edgeLevel_.back() > level) {
            edges_.pop_back();
            edgeLevel_.pop_back();
        }
        lastCycle_.clear();
    }

    void clear() {
        edges_.clear();
        edgeLevel_.clear();
        lastCycle_.clear();
        std::fill(pot_.begin(), pot_.end(), Weight{});
    }

private:
    // Build a DifferenceGraph of currently-enabled edges and run the proven
    // full Bellman-Ford (used only on the rare conflicting-edge path).
    BfResult<Weight> runFullOnEnabled() const {
        DifferenceGraph<Weight> g;
        for (int i = 1; i < numNodes(); ++i) g.getOrCreateNode(nodeToName_[i]);
        for (const auto& e : edges_) g.addEdge(e.from, e.to, e.weight, e.reason);
        BellmanFord<Weight> bf;
        return bf.runFull(g);
    }

    std::vector<std::string> nodeToName_;
    std::unordered_map<std::string, int> nameToNode_;
    std::vector<DlEdge<Weight>> edges_;
    std::vector<int> edgeLevel_;
    std::vector<Weight> pot_;
    std::vector<EdgeId> lastCycle_;
};

} // namespace zolver
