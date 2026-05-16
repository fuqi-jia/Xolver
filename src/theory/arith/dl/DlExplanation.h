#pragma once

#include "theory/TheorySolver.h"
#include "theory/arith/dl/DifferenceGraph.h"
#include <vector>
#include <unordered_set>

namespace nlcolver {

// ============================================================================
// Convert a negative cycle into a TheoryConflict clause.
// Each edge in the cycle carries a SatLit reason; the conflict is the
// disjunction of their negations.
// ============================================================================
template <typename Weight>
inline TheoryConflict buildConflict(const std::vector<EdgeId>& cycle,
                                    const DifferenceGraph<Weight>& graph) {
    std::vector<SatLit> lits;
    std::unordered_set<uint64_t> seen;
    for (EdgeId eid : cycle) {
        SatLit reason = graph.edge(eid).reason;
        uint64_t key = (static_cast<uint64_t>(reason.var) << 1) | (reason.sign ? 1u : 0u);
        if (seen.insert(key).second) {
            lits.push_back(reason);
        }
    }
    return TheoryConflict{std::move(lits)};
}

} // namespace nlcolver
