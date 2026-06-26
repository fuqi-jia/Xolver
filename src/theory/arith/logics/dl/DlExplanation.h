#pragma once

#include "theory/core/TheorySolver.h"
#include "theory/arith/logics/dl/DifferenceGraph.h"
#include <vector>
#include <unordered_set>
#ifdef XOLVER_ENABLE_PROOFS
#include "proof/TheoryProofSink.h"
#include "theory/core/TheoryAtomRegistry.h"
#endif

namespace xolver {

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

#ifdef XOLVER_ENABLE_PROOFS
// Phase C: push an la_generic Farkas certificate for a negative cycle. A simple
// negative cycle telescopes — summing each difference constraint (vi - vi+1 < wi)
// with UNIT multiplier 1 cancels every variable (each appears once +1, once -1)
// and leaves the constant Σwi, which is < 0 by the negative-cycle property, so the
// combination is contradictory by construction. The Solver's la_generic guard
// (positive + top-level + linear/sort-safe) keeps only the clean all-positive
// cycles; mixed-polarity or non-linear ones stay skeleton. No-op off the proof
// path. (Identical reason atoms are deduped to match buildConflict's clause.)
template <typename Weight>
inline void pushDlFarkasCert(const std::vector<EdgeId>& cycle,
                             const DifferenceGraph<Weight>& graph,
                             TheoryAtomRegistry* registry) {
    auto* sink = proof::activeProofSink();
    if (!sink || !registry) return;
    proof::TheoryConflictCert cert;
    cert.rule = "la_generic";
    std::unordered_set<uint64_t> seen;
    for (EdgeId eid : cycle) {
        SatLit reason = graph.edge(eid).reason;
        uint64_t key = (static_cast<uint64_t>(reason.var) << 1) | (reason.sign ? 1u : 0u);
        if (!seen.insert(key).second) continue;
        const TheoryAtomRecord* rec = registry->findBySatVar(reason.var);
        if (!rec) return;  // can't identify the atom -> emit none (skeleton)
        cert.lits.push_back({rec->exprId, reason.sign});
        cert.args.push_back("1");  // unit Farkas multiplier per cycle edge
    }
    if (!cert.lits.empty()) sink->addConflict(std::move(cert));
}
#endif

} // namespace xolver
