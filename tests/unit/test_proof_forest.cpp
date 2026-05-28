#include <doctest/doctest.h>
#include "theory/euf/ProofForest.h"
#include "theory/euf/EufTypes.h"
#include <algorithm>
#include <tuple>
#include <vector>

using namespace xolver;

namespace {
MergeReason asserted(uint32_t var) {
    MergeReason r;
    r.kind = MergeReasonKind::AssertedEquality;
    r.lit = SatLit{var, true};
    return r;
}

// The set of directed edges (child -> parent, labelIdx) currently in the forest.
// Roots (parentOf(t)==t) contribute no edge, so newly-allocated lone roots from
// rolled-back operations don't perturb the comparison.
std::vector<std::tuple<EufTermId, EufTermId, size_t>> edges(const ProofForest& pf) {
    std::vector<std::tuple<EufTermId, EufTermId, size_t>> out;
    for (EufTermId t = 0; t < pf.nodeCount(); ++t) {
        if (pf.parentOf(t) != t) {
            out.push_back({t, pf.parentOf(t), pf.labelIdxOf(t)});
        }
    }
    std::sort(out.begin(), out.end());
    return out;
}
} // namespace

TEST_CASE("ProofForest N-O: rollback restores edges byte-identical across interleaved ops") {
    ProofForest pf;
    pf.addEdge(0, 1, asserted(1));
    pf.addEdge(1, 2, asserted(2));

    size_t snap = pf.snapshot();
    auto before = edges(pf);

    // Further merges, including one that forces a makeRoot path-reversal (0 is
    // not a root of its tree, so addEdge(0,3,...) must re-root 0's tree).
    pf.addEdge(2, 3, asserted(3));
    pf.addEdge(0, 3, asserted(4));

    pf.rollback(snap);
    auto after = edges(pf);

    CHECK(before == after);
}

TEST_CASE("ProofForest N-O: nested push/pop-style rollback to multiple snapshots") {
    ProofForest pf;
    pf.addEdge(0, 1, asserted(1));
    size_t s1 = pf.snapshot();
    auto e1 = edges(pf);
    pf.addEdge(1, 2, asserted(2));
    size_t s2 = pf.snapshot();
    auto e2 = edges(pf);
    pf.addEdge(2, 3, asserted(3));
    pf.addEdge(3, 0, asserted(4));  // reversal

    pf.rollback(s2);
    CHECK(edges(pf) == e2);
    pf.rollback(s1);
    CHECK(edges(pf) == e1);
}

TEST_CASE("ProofForest N-O: path between connected terms returns the connecting edges") {
    ProofForest pf;
    pf.addEdge(0, 1, asserted(10));
    pf.addEdge(1, 2, asserted(20));
    pf.addEdge(3, 2, asserted(30));  // 3 attaches to 2's tree

    // 0 and 3 are connected: 0-1-2-3. The path must traverse exactly the three
    // edges, and edgeReason on each returned id must be the merge that created it.
    auto p = pf.path(0, 3);
    CHECK(p.size() == 3);

    std::vector<uint32_t> vars;
    for (size_t id : p) vars.push_back(pf.edgeReason(id).lit.var);
    std::sort(vars.begin(), vars.end());
    CHECK(vars == std::vector<uint32_t>{10, 20, 30});
}

TEST_CASE("ProofForest N-O: path is empty for identical / unconnected terms") {
    ProofForest pf;
    pf.addEdge(0, 1, asserted(1));
    pf.addEdge(2, 3, asserted(2));  // separate tree

    CHECK(pf.path(0, 0).empty());
    CHECK(pf.path(0, 2).empty());  // different trees
}
