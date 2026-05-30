#pragma once

#include "theory/arith/nia/NiaTypes.h"
#include "theory/arith/nia/preprocess/NiaNormalizer.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include <cstdint>
#include <gmpxx.h>
#include <optional>
#include <vector>

namespace xolver {

// A single congruence fact `lhs ≡ rhs (mod modulus)` carrying the SAT
// literals that justify it. The semantics are undirected: `lhs ≡ rhs (mod m)`
// is the same fact as `rhs ≡ lhs (mod m)`. `modulus` is a positive integer
// (Phase 2.7a focuses on numeric moduli; symbolic-modulus chains may follow
// in a later phase if Certora trace shapes require it).
//
// Reasons compose by *set union* — derived chain steps carry the union of
// their constituent edges' reason sets. The chain inference layer never
// invents reasons; it only composes existing ones.
struct ChainStep {
    PolyId lhs;
    PolyId rhs;
    mpz_class modulus;
    std::vector<SatLit> reasons;
};

// ChainGraph: an undirected multigraph of congruences modulo a single (or
// multiple, but compose only same-modulus edges) modulus. Edges are
// ChainSteps. Closure under transitivity is bounded by a depth budget to
// prevent combinatorial explosion on the Certora EVM chains
// (state_{n+1} ≡ f(state_n) mod 2^256). The depth cap is the maximum number
// of original edges combined in any derived step.
//
// Soundness invariant: closeTransitive only composes edges with identical
// modulus, and the composed reason set is the union of the source reason
// sets. Therefore every derived step's reason set is complete — it implies
// the derived congruence under the original constraint system.
class ChainGraph {
public:
    ChainGraph() = default;

    void addEdge(const ChainStep& step) { edges_.push_back(step); }

    const std::vector<ChainStep>& edges() const { return edges_; }

    // Extend the edge set with all derivable congruences up to depth
    // `maxDepth` (counts the number of *original* edges combined). For
    // maxDepth=1, no new edges are added (the original set is already at
    // depth 1). For maxDepth=2, every pair of edges sharing a node and
    // modulus produces a derived edge. Iterates until fixpoint or budget.
    //
    // The caller may cap the total number of derived edges via
    // `derivedBudget` to keep BFS bounded on Certora-scale chains. When the
    // budget is hit, BFS terminates early — this is a completeness drop, not
    // a soundness violation: every edge still in the graph is still implied.
    void closeTransitive(int maxDepth, std::size_t derivedBudget = 4096);

    // Find the first edge whose endpoints (in either direction) match the
    // given lhs/rhs at the given modulus. PolyId equality is used directly:
    // callers are expected to canonicalize via the kernel before querying.
    // Returns nullopt if no such edge exists.
    std::optional<ChainStep> findStep(PolyId lhs, PolyId rhs,
                                      const mpz_class& modulus) const;

private:
    std::vector<ChainStep> edges_;
};

// Compose two congruence steps sharing an endpoint and the same modulus.
// Returns nullopt if the endpoints don't align or moduli differ. The
// composed step's reason set is the union of inputs (de-duplicated by
// SatLit equality). Pure helper — no kernel work.
std::optional<ChainStep> composeChainSteps(const ChainStep& a,
                                           const ChainStep& b);

} // namespace xolver
