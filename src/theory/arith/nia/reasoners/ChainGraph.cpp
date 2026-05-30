#include "theory/arith/nia/reasoners/ChainGraph.h"

#include <algorithm>

namespace xolver {

namespace {

// Dedupe reason list in-place by SatLit equality. The list is typically
// short (≤ chain depth × original-edge reasons), so O(n^2) dedupe is fine.
void dedupeReasons(std::vector<SatLit>& rs) {
    for (std::size_t i = 0; i < rs.size(); ++i) {
        for (std::size_t j = i + 1; j < rs.size(); ) {
            if (rs[i] == rs[j]) {
                rs.erase(rs.begin() + static_cast<std::ptrdiff_t>(j));
            } else {
                ++j;
            }
        }
    }
}

// Union two reason lists, preserving order from `a` then appending novel
// entries from `b`. Linear pass — see dedupeReasons.
std::vector<SatLit> unionReasons(const std::vector<SatLit>& a,
                                  const std::vector<SatLit>& b) {
    std::vector<SatLit> out = a;
    out.reserve(a.size() + b.size());
    for (const SatLit& r : b) {
        bool found = false;
        for (const SatLit& q : out) {
            if (q == r) { found = true; break; }
        }
        if (!found) out.push_back(r);
    }
    return out;
}

} // namespace

std::optional<ChainStep> composeChainSteps(const ChainStep& a,
                                            const ChainStep& b) {
    if (a.modulus != b.modulus) return std::nullopt;
    // Try every endpoint alignment of two undirected edges. Each successful
    // alignment yields the same composed reason set (union), but the
    // resulting (lhs, rhs) pair differs.
    PolyId newLhs = NullPoly, newRhs = NullPoly;
    if (a.rhs == b.lhs) { newLhs = a.lhs; newRhs = b.rhs; }
    else if (a.rhs == b.rhs) { newLhs = a.lhs; newRhs = b.lhs; }
    else if (a.lhs == b.lhs) { newLhs = a.rhs; newRhs = b.rhs; }
    else if (a.lhs == b.rhs) { newLhs = a.rhs; newRhs = b.lhs; }
    else return std::nullopt;
    if (newLhs == newRhs) return std::nullopt;  // trivial self-edge
    ChainStep out;
    out.lhs = newLhs;
    out.rhs = newRhs;
    out.modulus = a.modulus;
    out.reasons = unionReasons(a.reasons, b.reasons);
    dedupeReasons(out.reasons);
    return out;
}

void ChainGraph::closeTransitive(int maxDepth, std::size_t derivedBudget) {
    if (maxDepth <= 1) return;
    // Track the depth (= number of original edges combined) of each edge so
    // we don't double-compose past the budget. Initial edges have depth 1.
    std::vector<int> depth(edges_.size(), 1);
    std::size_t derivedCount = 0;

    // Iterative deepening: at each round, compose edges where (depthA +
    // depthB) ≤ maxDepth, against the current edge set. Stop at fixpoint or
    // when the budget is exhausted.
    while (derivedCount < derivedBudget) {
        bool added = false;
        const std::size_t snapshot = edges_.size();
        for (std::size_t i = 0; i < snapshot; ++i) {
            for (std::size_t j = i + 1; j < snapshot; ++j) {
                if (depth[i] + depth[j] > maxDepth) continue;
                auto composed = composeChainSteps(edges_[i], edges_[j]);
                if (!composed) continue;
                // Skip if an equivalent edge (same endpoints + modulus)
                // already exists. Equivalence is endpoint-set equality
                // (undirected) — soundness only requires that we not
                // explode the edge count with duplicates.
                bool dupe = false;
                for (const ChainStep& e : edges_) {
                    if (e.modulus != composed->modulus) continue;
                    if ((e.lhs == composed->lhs && e.rhs == composed->rhs) ||
                        (e.lhs == composed->rhs && e.rhs == composed->lhs)) {
                        dupe = true;
                        break;
                    }
                }
                if (dupe) continue;
                edges_.push_back(*composed);
                depth.push_back(depth[i] + depth[j]);
                added = true;
                if (++derivedCount >= derivedBudget) return;
            }
        }
        if (!added) return;
    }
}

std::optional<ChainStep> ChainGraph::findStep(PolyId lhs, PolyId rhs,
                                               const mpz_class& modulus) const {
    for (const ChainStep& e : edges_) {
        if (e.modulus != modulus) continue;
        if ((e.lhs == lhs && e.rhs == rhs) ||
            (e.lhs == rhs && e.rhs == lhs)) {
            return e;
        }
    }
    return std::nullopt;
}

} // namespace xolver
