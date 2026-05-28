// Cross-validate IncrementalDiffGraph (stateful potential + lazy full-BF) against
// the proven full Bellman-Ford oracle on random difference-constraint sequences.
// Soundness lock: the incremental feasibility verdict must MATCH full-BF after
// every edge, and whenever it reports feasible the maintained potential must
// actually satisfy every enabled edge (slack >= 0).

#include <doctest/doctest.h>
#include "theory/arith/dl/IncrementalDiffGraph.h"
#include "theory/arith/dl/DifferenceGraph.h"
#include "theory/arith/dl/BellmanFord.h"
#include "sat/SatSolver.h"
#include <random>
#include <vector>

using namespace xolver;

namespace {

struct E { int from; int to; long w; };

// Full-BF feasibility over an explicit edge list (the oracle).
bool fullFeasibleIdl(int nNodes, const std::vector<E>& edges) {
    DifferenceGraph<IdlWeight> g;
    for (int i = 1; i < nNodes; ++i) g.getOrCreateNode("v" + std::to_string(i));
    for (const auto& e : edges) g.addEdge(e.from, e.to, IdlWeight(e.w), SatLit{1, true});
    BellmanFord<IdlWeight> bf;
    return !bf.runFull(g).negativeCycle;
}

} // namespace

TEST_CASE("IncrementalDiffGraph: verdict matches full Bellman-Ford (IDL, random)") {
    std::mt19937 rng(12345);
    const int K = 7;                 // nodes 0..K-1 (0 = ZERO)
    const int STEPS = 25;
    const int TRIALS = 1500;

    int feasObserved = 0, infeasObserved = 0;

    for (int t = 0; t < TRIALS; ++t) {
        IncrementalDiffGraph<IdlWeight> ig;
        for (int i = 1; i < K; ++i) ig.getOrCreateNode("v" + std::to_string(i));

        std::vector<E> edges;   // currently-enabled edges (mirrors ig)
        std::uniform_int_distribution<int> nodeD(0, K - 1);
        std::uniform_int_distribution<int> wD(-3, 3);

        for (int s = 0; s < STEPS; ++s) {
            int from = nodeD(rng), to = nodeD(rng);
            if (from == to) continue;
            long w = wD(rng);

            bool incFeasible = ig.enableEdge(from, to, IdlWeight(w), SatLit{1, true}, s);
            edges.push_back({from, to, w});

            bool fullFeasible = fullFeasibleIdl(K, edges);
            REQUIRE(incFeasible == fullFeasible);

            if (!incFeasible) {
                ++infeasObserved;
                // Mirror the solver: backtrack the conflicting edge and continue.
                ig.backtrack(s - 1);
                edges.pop_back();
            } else {
                ++feasObserved;
                // The maintained potential must satisfy every enabled edge.
                for (const auto& e : edges) {
                    IdlWeight slack = ig.potential(e.to) - ig.potential(e.from);
                    CHECK(slack <= IdlWeight(e.w));
                }
            }
        }
    }
    // Sanity: the random suite exercised both verdicts.
    CHECK(feasObserved > 0);
    CHECK(infeasObserved > 0);
}

TEST_CASE("IncrementalDiffGraph: RDL strict edges + backtrack restores feasibility") {
    // x - y < 0  (edge y->x weight (0,-1)) and y - x < 0 (edge x->y weight (0,-1))
    // => strict cycle, infeasible. Backtrack one => feasible again.
    IncrementalDiffGraph<RdlWeight> ig;
    int x = ig.getOrCreateNode("x");
    int y = ig.getOrCreateNode("y");

    bool f1 = ig.enableEdge(y, x, RdlWeight(0, -1), SatLit{1, true}, 1);  // x < y? edge y->x: x <= y - δ
    CHECK(f1);
    bool f2 = ig.enableEdge(x, y, RdlWeight(0, -1), SatLit{2, true}, 2);  // y <= x - δ : strict negative cycle
    CHECK_FALSE(f2);

    ig.backtrack(1);  // drop the second edge
    // Re-add a feasible edge: y - x <= 5
    bool f3 = ig.enableEdge(x, y, RdlWeight(5, 0), SatLit{3, true}, 2);
    CHECK(f3);
    // potential must satisfy both enabled edges (x<=y-δ and y<=x+5).
    CHECK((ig.potential(x) - ig.potential(y)) <= RdlWeight(0, -1));
    CHECK((ig.potential(y) - ig.potential(x)) <= RdlWeight(5, 0));
}
