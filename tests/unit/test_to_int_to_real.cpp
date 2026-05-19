#include <doctest/doctest.h>
#include "expr/ir.h"
#include "frontend/preprocess/ArithCastNormalizer.h"
#include "frontend/preprocess/LinearToIntPurifier.h"
#include "expr/Smt2Dumper.h"
#include <iostream>

using namespace nlcolver;

TEST_CASE("ArithCastNormalizer: to_real(ConstInt)") {
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

    ExprId three = ir.add(CoreExpr{Kind::ConstInt, intSort, {}, Payload(int64_t(3))});
    ExprId toRealThree = ir.add(CoreExpr{Kind::ToReal, realSort, {three}, {}});
    ExprId eq = ir.add(CoreExpr{Kind::Eq, boolSort, {toRealThree, toRealThree}, {}});
    ir.addAssertion(eq);

    ArithCastNormalizer norm(ir);
    auto result = norm.run();
    REQUIRE(result.assertions.size() == 1);

    const auto& lowered = ir.get(result.assertions[0].second);
    // to_real(3) should be folded to ConstReal "3"
    REQUIRE(lowered.kind == Kind::Eq);
    REQUIRE(lowered.children.size() == 2);
    const auto& lhs = ir.get(lowered.children[0]);
    REQUIRE(lhs.kind == Kind::ConstReal);
}

TEST_CASE("ArithCastNormalizer: to_int(ConstReal)") {
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

    ExprId threePointSeven = ir.add(CoreExpr{Kind::ConstReal, realSort, {}, Payload(std::string("37/10"))});
    ExprId toInt = ir.add(CoreExpr{Kind::ToInt, intSort, {threePointSeven}, {}});
    ExprId three = ir.add(CoreExpr{Kind::ConstInt, intSort, {}, Payload(int64_t(3))});
    ExprId eq = ir.add(CoreExpr{Kind::Eq, boolSort, {toInt, three}, {}});
    ir.addAssertion(eq);

    ArithCastNormalizer norm(ir);
    auto result = norm.run();
    REQUIRE(result.assertions.size() == 1);

    const auto& lowered = ir.get(result.assertions[0].second);
    REQUIRE(lowered.kind == Kind::Eq);
    const auto& lhs = ir.get(lowered.children[0]);
    REQUIRE(lhs.kind == Kind::ConstInt);
    auto* v = std::get_if<int64_t>(&lhs.payload.value);
    REQUIRE(v != nullptr);
    REQUIRE(*v == 3);
}

TEST_CASE("LinearToIntPurifier: detectOnly linear to_int") {
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

    ExprId x = ir.add(CoreExpr{Kind::Variable, realSort, {}, Payload(std::string("x"))});
    ExprId toInt = ir.add(CoreExpr{Kind::ToInt, intSort, {x}, {}});
    ExprId three = ir.add(CoreExpr{Kind::ConstInt, intSort, {}, Payload(int64_t(3))});
    ExprId eq = ir.add(CoreExpr{Kind::Eq, boolSort, {toInt, three}, {}});
    ir.addAssertion(eq);

    LinearToIntPurifier purifier(ir);
    auto detect = purifier.detectOnly();
    REQUIRE(!detect.hasUnsupportedNonlinearToInt);
}

TEST_CASE("LinearToIntPurifier: detectOnly nonlinear to_int") {
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

    ExprId x = ir.add(CoreExpr{Kind::Variable, realSort, {}, Payload(std::string("x"))});
    ExprId mul = ir.add(CoreExpr{Kind::Mul, realSort, {x, x}, {}});
    ExprId toInt = ir.add(CoreExpr{Kind::ToInt, intSort, {mul}, {}});
    ExprId three = ir.add(CoreExpr{Kind::ConstInt, intSort, {}, Payload(int64_t(3))});
    ExprId eq = ir.add(CoreExpr{Kind::Eq, boolSort, {toInt, three}, {}});
    ir.addAssertion(eq);

    LinearToIntPurifier purifier(ir);
    auto detect = purifier.detectOnly();
    REQUIRE(detect.hasUnsupportedNonlinearToInt);
}

TEST_CASE("LinearToIntPurifier: run creates floor lemmas") {
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

    ExprId x = ir.add(CoreExpr{Kind::Variable, realSort, {}, Payload(std::string("x"))});
    ExprId toInt = ir.add(CoreExpr{Kind::ToInt, intSort, {x}, {}});
    ExprId three = ir.add(CoreExpr{Kind::ConstInt, intSort, {}, Payload(int64_t(3))});
    ExprId eq = ir.add(CoreExpr{Kind::Eq, boolSort, {toInt, three}, {}});
    ir.addAssertion(eq);

    LinearToIntPurifier purifier(ir);
    auto result = purifier.run();

    REQUIRE(!result.hasUnsupportedNonlinearToInt);
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

TEST_CASE("LinearToIntPurifier: cache dedup same to_int") {
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

    ExprId x = ir.add(CoreExpr{Kind::Variable, realSort, {}, Payload(std::string("x"))});
    ExprId toInt1 = ir.add(CoreExpr{Kind::ToInt, intSort, {x}, {}});
    ExprId toInt2 = ir.add(CoreExpr{Kind::ToInt, intSort, {x}, {}});
    ExprId add = ir.add(CoreExpr{Kind::Add, intSort, {toInt1, toInt2}, {}});
    ExprId eq = ir.add(CoreExpr{Kind::Eq, boolSort, {add, add}, {}});
    ir.addAssertion(eq);

    LinearToIntPurifier purifier(ir);
    auto result = purifier.run();
    REQUIRE(result.infos.size() == 1); // same x should share same k
}
