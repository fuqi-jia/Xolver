#include <doctest/doctest.h>
#include "expr/ir.h"
#include "frontend/preprocess/LinearToIntPurifier.h"
#include <iostream>

using namespace nlcolver;

TEST_CASE("Simple purify test") {
    CoreIr ir;
    SortId boolSort = ir.allocateSortId();
    ir.registerSort(boolSort, SortKind::Bool);
    ir.setBoolSortId(boolSort);
    SortId intSort = ir.allocateSortId();
    ir.registerSort(intSort, SortKind::Int);
    ir.setIntSortId(intSort);
    SortId realSort = ir.allocateSortId();
    ir.registerSort(realSort, SortKind::Real);
    ir.setRealSortId(realSort);

    // Build: (= (to_int x) 3)
    ExprId x = ir.add(CoreExpr{Kind::Variable, realSort, {}, Payload(std::string("x"))});
    ExprId toInt = ir.add(CoreExpr{Kind::ToInt, intSort, {x}, {}});
    ExprId three = ir.add(CoreExpr{Kind::ConstInt, intSort, {}, Payload(int64_t(3))});
    ExprId eq = ir.add(CoreExpr{Kind::Eq, boolSort, {toInt, three}, {}});
    ir.addAssertion(eq);

    LinearToIntPurifier purifier(ir);
    auto detect = purifier.detectOnly();
    REQUIRE(!detect.hasUnsupportedNonlinearToInt);

    auto result = purifier.run();
    REQUIRE(result.purifiedAssertions.size() == 1);
    REQUIRE(result.floorLemmas.size() == 2);
    REQUIRE(result.infos.size() == 1);

    // Check purified assertion is (= k 3)
    const auto& pa = ir.get(result.purifiedAssertions[0].second);
    REQUIRE(pa.kind == Kind::Eq);
    const auto& lhs = ir.get(pa.children[0]);
    REQUIRE(lhs.kind == Kind::Variable);
    REQUIRE(lhs.sort == intSort);

    // Check floor lemmas
    const auto& lower = ir.get(result.floorLemmas[0].second);
    const auto& upper = ir.get(result.floorLemmas[1].second);
    REQUIRE(lower.kind == Kind::Leq);
    REQUIRE(upper.kind == Kind::Lt);
}
