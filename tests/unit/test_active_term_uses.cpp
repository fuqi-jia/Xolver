#include "ir/ActiveTermUses.h"
#include <doctest/doctest.h>
#include <functional>

using namespace xolver;

namespace {
ExprId leaf(NativeTerms& ir, const std::string& name) {
    if (ir.boolSortId() == NullSort) {
        ir.registerSort(0, SortKind::Bool);
        ir.setBoolSortId(0);
    }
    return ir.add({Kind::Variable, 0, {}, Payload(name)});
}
ExprId pair(NativeTerms& ir, ExprId left, ExprId right) {
    return ir.addShared({Kind::And, 0, {left, right}, {}});
}
}

TEST_CASE("Active term uses: shared edges and duplicate root slots withdraw independently") {
    NativeTerms ir;
    const auto x = leaf(ir, "x"), y = leaf(ir, "y");
    const auto shared = pair(ir, x, x);
    const auto root = pair(ir, shared, y);
    ActiveTermUses uses(ir);
    uses.setRoot(0, root);
    uses.setRoot(1, root);
    CHECK((uses.variableClosure("x").roots == std::vector<size_t>{0, 1}));
    uses.setRoot(0, shared);
    CHECK((uses.variableClosure("y").roots == std::vector<size_t>{1}));
    uses.setRoot(1, NullExpr);
    CHECK(uses.variableClosure("y").terms.empty());
    CHECK_FALSE(uses.variableClosure("x").terms.contains(root));
    uses.setRoot(0, NullExpr);
    CHECK(uses.variableClosure("x").terms.empty());
    uses.setRoot(2, root);
    CHECK((uses.variableClosure("x").roots == std::vector<size_t>{2}));
    const auto anotherX = leaf(ir, "x");
    REQUIRE(anotherX != x);
    uses.setRoot(3, anotherX);
    CHECK((uses.variableClosure("x").roots == std::vector<size_t>{2, 3}));
    CHECK(uses.variableClosure("missing").roots.empty());
}

TEST_CASE("Active term uses: exact closures agree with independent forward traversal after replacements") {
    NativeTerms ir;
    std::vector<ExprId> nodes;
    for (int index = 0; index < 8; ++index) nodes.push_back(leaf(ir, "v" + std::to_string(index)));
    for (size_t index = 0; index < 80; ++index)
        nodes.push_back(pair(ir, nodes[(index * 13 + 3) % nodes.size()],
                                 nodes[(index * 7 + 1) % nodes.size()]));
    ActiveTermUses uses(ir);
    std::vector<ExprId> roots(5, NullExpr);
    for (size_t round = 0; round < 120; ++round) {
        const auto slot = round % roots.size();
        roots[slot] = round % 7 == 0 ? NullExpr : nodes[(round * 17 + 9) % nodes.size()];
        uses.setRoot(slot, roots[slot]);
        for (int variable = 0; variable < 8; ++variable) {
            const auto name = "v" + std::to_string(variable);
            std::unordered_map<ExprId, bool> memo;
            std::function<bool(ExprId)> contains = [&](ExprId id) {
                if (memo.contains(id)) return memo.at(id);
                const auto& node = ir.get(id);
                bool result = node.kind == Kind::Variable &&
                    std::get<std::string>(node.payload.value) == name;
                for (const auto child : node.children) {
                    const bool found = contains(child);
                    result = found || result;
                }
                memo[id] = result;
                return result;
            };
            std::vector<size_t> expectedRoots;
            for (size_t index = 0; index < roots.size(); ++index)
                if (roots[index] != NullExpr && contains(roots[index])) expectedRoots.push_back(index);
            std::unordered_set<ExprId> expectedTerms;
            for (const auto& [id, found] : memo) if (found) expectedTerms.insert(id);
            const auto closure = uses.variableClosure(name);
            CHECK(closure.roots == expectedRoots);
            CHECK(closure.terms == expectedTerms);
        }
    }
}

TEST_CASE("Active term uses: unrelated roots do not enter a variable query") {
    NativeTerms ir;
    ActiveTermUses uses(ir);
    ExprId first = NullExpr;
    for (size_t index = 0; index < 400; ++index) {
        const auto value = leaf(ir, "v" + std::to_string(index));
        if (index == 0) first = value;
        uses.setRoot(index, pair(ir, value, value));
    }
    const auto before = uses.work();
    const auto closure = uses.variableClosure("v0");
    CHECK((closure.roots == std::vector<size_t>{0}));
    CHECK(closure.terms.size() == 2);
    CHECK(closure.terms.contains(first));
    CHECK(uses.work() - before == 2);
}

TEST_CASE("Active term uses: deep DAG activation and removal are iterative") {
    NativeTerms ir;
    const auto x = leaf(ir, "x");
    auto root = x;
    for (int index = 0; index < 4000; ++index) root = pair(ir, root, root);
    ActiveTermUses uses(ir);
    uses.setRoot(0, root);
    CHECK(uses.variableClosure("x").terms.size() == 4001);
    uses.setRoot(0, NullExpr);
    CHECK(uses.variableClosure("x").terms.empty());
}
