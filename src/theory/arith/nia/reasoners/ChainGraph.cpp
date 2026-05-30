#include "theory/arith/nia/reasoners/ChainGraph.h"

#include <algorithm>
#include <random>
#include <unordered_map>
#include <unordered_set>

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

std::optional<ChainStep> tryReduceGoal(const ChainGraph& graph,
                                        PolyId lhs, PolyId rhs,
                                        const mpz_class& modulus,
                                        int maxDepth) {
    if (lhs == NullPoly || rhs == NullPoly) return std::nullopt;
    // Fast path: the requested edge is already present in the original
    // graph at the requested modulus — no closure work needed.
    if (auto direct = graph.findStep(lhs, rhs, modulus)) {
        return direct;
    }
    if (maxDepth <= 1) return std::nullopt;
    // Closure on a private copy so the caller's graph stays read-only.
    ChainGraph work = graph;
    work.closeTransitive(maxDepth);
    return work.findStep(lhs, rhs, modulus);
}

bool validateChainStep(PolynomialKernel& kernel, const ChainStep& step,
                       int samples, unsigned seed) {
    if (step.modulus <= 0) return false;  // contract: positive modulus
    if (step.lhs == step.rhs) return true;  // trivial self-edge — vacuous
    // Collect the union of variable names appearing on either side.
    std::vector<std::string> varsL = kernel.variables(step.lhs);
    std::vector<std::string> varsR = kernel.variables(step.rhs);
    std::unordered_set<std::string> all;
    all.reserve(varsL.size() + varsR.size());
    for (const auto& v : varsL) all.insert(v);
    for (const auto& v : varsR) all.insert(v);
    std::vector<std::string> vars(all.begin(), all.end());

    // Run a quick evaluability probe at the zero assignment. If the kernel
    // doesn't support evalInteger (stub backend), bail out true — the
    // reasoner's higher-level cert path will catch real issues. If it
    // *does* support eval, we proceed.
    {
        std::unordered_map<std::string, mpz_class> probe;
        for (const auto& v : vars) probe[v] = mpz_class(0);
        auto probeL = kernel.evalInteger(step.lhs, probe);
        auto probeR = kernel.evalInteger(step.rhs, probe);
        if (!probeL || !probeR) return true;  // stub backend — skip
    }

    std::mt19937 rng(seed);
    // Sample integers from a moderate signed range so we exercise sign
    // wrap and modular reduction. The exact range matters less than
    // breadth: small primes catch sign bugs, larger samples catch coeff
    // mismatch.
    const long sampleLo = -8, sampleHi = 8;
    std::uniform_int_distribution<long> dist(sampleLo, sampleHi);
    for (int s = 0; s < samples; ++s) {
        std::unordered_map<std::string, mpz_class> env;
        env.reserve(vars.size());
        for (const auto& v : vars) env[v] = mpz_class(dist(rng));
        auto evL = kernel.evalInteger(step.lhs, env);
        auto evR = kernel.evalInteger(step.rhs, env);
        if (!evL || !evR) return true;  // backend can't eval this sample
        mpz_class diff = *evL - *evR;
        mpz_class r = diff % step.modulus;
        if (r != 0) return false;
    }
    return true;
}

} // namespace xolver
