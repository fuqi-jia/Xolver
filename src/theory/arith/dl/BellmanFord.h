#pragma once

#include "theory/arith/dl/DifferenceGraph.h"
#include <vector>
#include <limits>

namespace zolver {

// ============================================================================
// Bellman-Ford result: potentials or a negative cycle.
// ============================================================================
template <typename Weight>
struct BfResult {
    bool negativeCycle = false;
    std::vector<EdgeId> cycle;
    std::vector<Weight> dist;
};

// ============================================================================
// Bellman-Ford shortest paths for difference constraint feasibility.
// All potentials initialized to 0 (standard for detecting negative cycles).
// ============================================================================
template <typename Weight>
class BellmanFord {
public:
    BfResult<Weight> runFull(const DifferenceGraph<Weight>& graph) {
        int n = graph.numNodes();
        BfResult<Weight> result;
        result.dist.assign(n, Weight{});
        std::vector<EdgeId> pred(n, std::numeric_limits<EdgeId>::max());

        for (int i = 1; i <= n; ++i) {
            bool changed = false;
            for (const auto& e : graph.edges()) {
                // Relax: dist[to] > dist[from] + weight ?
                Weight cand = result.dist[e.from] + e.weight;
                if (cand < result.dist[e.to]) {
                    result.dist[e.to] = cand;
                    pred[e.to] = e.id;
                    changed = true;
                    if (i == n) {
                        // Negative cycle detected
                        result.negativeCycle = true;
                        result.cycle = extractCycle(graph, pred, e.to, n);
                        return result;
                    }
                }
            }
            if (!changed) break;
        }

        return result;
    }

private:
    std::vector<EdgeId> extractCycle(const DifferenceGraph<Weight>& graph,
                                     const std::vector<EdgeId>& pred,
                                     int startNode, int n) {
        // Walk back n steps to reach a node on the cycle
        int x = startNode;
        for (int i = 0; i < n; ++i) {
            EdgeId eid = pred[x];
            if (eid == std::numeric_limits<EdgeId>::max()) break;
            x = graph.edge(eid).from;
        }

        // Now x is on the cycle; collect cycle edges
        std::vector<EdgeId> cycle;
        int cycleStart = x;
        do {
            EdgeId eid = pred[x];
            cycle.push_back(eid);
            x = graph.edge(eid).from;
        } while (x != cycleStart);

        return cycle;
    }
};

} // namespace zolver
