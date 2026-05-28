#pragma once

#include "theory/arith/dl/DifferenceGraph.h"
#include <unordered_map>
#include <string>

namespace xolver {

// ============================================================================
// Build an integer model from Bellman-Ford potentials.
// model(x) = potential(x) - potential(ZERO)
// ============================================================================
inline std::unordered_map<std::string, mpz_class>
buildIdlModel(const std::vector<mpz_class>& dist,
              int zeroNode,
              const DifferenceGraph<mpz_class>& graph) {
    std::unordered_map<std::string, mpz_class> model;
    model[graph.nodeName(zeroNode)] = 0;
    for (int i = 0; i < graph.numNodes(); ++i) {
        if (i == zeroNode) continue;
        model[graph.nodeName(i)] = dist[i] - dist[zeroNode];
    }
    return model;
}

// ============================================================================
// Build a rational model from Bellman-Ford delta-potentials.
// Chooses a concrete epsilon > 0 and instantiates delta = epsilon.
// Returns nullopt if no feasible epsilon can be found (indicates internal error).
// ============================================================================
inline std::optional<std::unordered_map<std::string, mpq_class>>
buildRdlModel(const std::vector<RdlWeight>& dist,
              int zeroNode,
              const DifferenceGraph<RdlWeight>& graph) {
    // For each edge u->v with weight C+Dδ and potentials:
    //   dist[v] = A_v + B_vδ, dist[u] = A_u + B_uδ
    // After substituting δ=ε we need:
    //   (A_v - A_u - C) + (B_v - B_u - D) ε <= 0
    // Let P = A_v - A_u - C, Q = B_v - B_u - D.
    // Bellman-Ford guarantees (P, Q) <= (0, 0) lexicographically.

    std::optional<mpq_class> upper;  // collected positive upper bound on ε

    for (const auto& e : graph.edges()) {
        const RdlWeight& dv = dist[e.to];
        const RdlWeight& du = dist[e.from];

        mpq_class P = dv.c - du.c - e.weight.c;
        int Q = dv.deltaCoeff - du.deltaCoeff - e.weight.deltaCoeff;

        if (P > 0) {
            return std::nullopt;
        }

        if (P == 0) {
            if (Q > 0) {
                return std::nullopt;
            }
            continue;
        }

        // P < 0
        if (Q > 0) {
            mpq_class bound = (-P) / Q;
            if (!upper || bound < *upper) {
                upper = bound;
            }
        }
    }

    mpq_class epsilon;
    if (upper) {
        if (*upper <= 0) {
            return std::nullopt;
        }
        epsilon = *upper / 2;
    } else {
        epsilon = 1;
    }

    std::unordered_map<std::string, mpq_class> model;
    model[graph.nodeName(zeroNode)] = 0;
    for (int i = 0; i < graph.numNodes(); ++i) {
        if (i == zeroNode) continue;
        const std::string& name = graph.nodeName(i);
        if (name.empty()) continue;
        model[name] = (dist[i].c - dist[zeroNode].c)
                    + (dist[i].deltaCoeff - dist[zeroNode].deltaCoeff) * epsilon;
    }

    return model;
}

} // namespace xolver
