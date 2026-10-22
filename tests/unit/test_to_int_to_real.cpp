#include <doctest/doctest.h>
#include "ir/NativeTerms.h"
#include "frontend/preprocess/ArithCastNormalizer.h"
#include "frontend/preprocess/ToIntDefinitionalLowerer.h"
#include "ir/Smt2Dumper.h"
#include <iostream>

using namespace xolver;

namespace {

void setupBasicSorts(NativeTerms& ir, SortId& boolSort, SortId& intSort, SortId& realSort) {
    boolSort = ir.allocateSortId();
    ir.registerSort(boolSort, SortKind::Bool);
    ir.setBoolSortId(boolSort);
    intSort = ir.allocateSortId();
    ir.registerSort(intSort, SortKind::Int);
    ir.setIntSortId(intSort);
    realSort = ir.allocateSortId();
    ir.registerSort(realSort, SortKind::Real);
    ir.setRealSortId(realSort);
}

} // namespace

TEST_CASE("ArithCastNormalizer: wide real-context node survives ir_.add realloc") {
    // The second visit rebuilds a Real-sorted node's children, calling ir_.add()
    // per Int-constant child to coerce it to ConstReal. The coercion loop iterated
    // `node.children` while holding `const auto& node` into exprs_, which ir_.add()
    // reallocates -> dangling range-for iterator (use-after-realloc SIGSEGV, the
    // same class as UCP substituteAssertion). Value-copying `node` fixes it. A wide
    // (zero-nesting) node can only crash via realloc, not recursion.
    constexpr int kWide = 4000;
    NativeTerms ir;
    SortId boolSort, intSort, realSort;
    setupBasicSorts(ir, boolSort, intSort, realSort);
    TermExpr wideAdd; wideAdd.kind = Kind::Add; wideAdd.sort = realSort;  // Real context
    for (int k = 0; k < kWide; ++k)
        wideAdd.children.push_back(
            ir.add(TermExpr{Kind::ConstInt, intSort, {}, Payload(int64_t(k))}));
    ExprId addId = ir.add(std::move(wideAdd));
    ExprId zero = ir.add(TermExpr{Kind::ConstReal, realSort, {}, Payload(std::string("0"))});
    ir.addAssertion(ir.add(TermExpr{Kind::Geq, boolSort, {addId, zero}, {}}));
    ArithCastNormalizer norm(ir);
    norm.run();   // former: SIGSEGV from dangling node.children iterator mid-coercion
    CHECK(true);
}

TEST_CASE("ArithCastNormalizer: to_real(ConstInt)") {
    NativeTerms ir;
    SortId boolSort, intSort, realSort;
    setupBasicSorts(ir, boolSort, intSort, realSort);

    ExprId three = ir.add(TermExpr{Kind::ConstInt, intSort, {}, Payload(int64_t(3))});
    ExprId toRealThree = ir.add(TermExpr{Kind::ToReal, realSort, {three}, {}});
    ExprId eq = ir.add(TermExpr{Kind::Eq, boolSort, {toRealThree, toRealThree}, {}});
    ir.addAssertion(eq);

    ArithCastNormalizer norm(ir);
    auto result = norm.run();
    REQUIRE(result.assertions.size() == 1);

    const auto& lowered = ir.get(result.assertions[0].second);
    REQUIRE(lowered.kind == Kind::Eq);
    REQUIRE(lowered.children.size() == 2);
    const auto& lhs = ir.get(lowered.children[0]);
    REQUIRE(lhs.kind == Kind::ConstReal);
}

TEST_CASE("ArithCastNormalizer: to_int(ConstReal)") {
    NativeTerms ir;
    SortId boolSort, intSort, realSort;
    setupBasicSorts(ir, boolSort, intSort, realSort);

    ExprId threePointSeven = ir.add(TermExpr{Kind::ConstReal, realSort, {}, Payload(std::string("37/10"))});
    ExprId toInt = ir.add(TermExpr{Kind::ToInt, intSort, {threePointSeven}, {}});
    ExprId three = ir.add(TermExpr{Kind::ConstInt, intSort, {}, Payload(int64_t(3))});
    ExprId eq = ir.add(TermExpr{Kind::Eq, boolSort, {toInt, three}, {}});
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

TEST_CASE("ToIntDefinitionalLowerer: linear to_int succeeds and emits bridge") {
    NativeTerms ir;
    SortId boolSort, intSort, realSort;
    setupBasicSorts(ir, boolSort, intSort, realSort);

    ExprId x = ir.add(TermExpr{Kind::Variable, realSort, {}, Payload(std::string("x"))});
    ExprId toInt = ir.add(TermExpr{Kind::ToInt, intSort, {x}, {}});
    ExprId three = ir.add(TermExpr{Kind::ConstInt, intSort, {}, Payload(int64_t(3))});
    ExprId eq = ir.add(TermExpr{Kind::Eq, boolSort, {toInt, three}, {}});
    ir.addAssertion(eq);

    ToIntDefinitionalLowerer t2i(ir);
    REQUIRE(t2i.run());
    REQUIRE(t2i.didLower());
    REQUIRE_FALSE(t2i.hadNonlinearBridge());
    t2i.commit();

    // After commit, assertion list = [rewritten eq, bridge, lower, upper].
    auto scoped = ir.getScopedAssertions();
    REQUIRE(scoped.size() == 4);
    const auto& rewritten = ir.get(scoped[0].second);
    REQUIRE(rewritten.kind == Kind::Eq);
    const auto& lhs = ir.get(rewritten.children[0]);
    REQUIRE(lhs.kind == Kind::Variable);
    REQUIRE(lhs.sort == intSort);
    // bridge equality r_t = x
    const auto& bridge = ir.get(scoped[1].second);
    REQUIRE(bridge.kind == Kind::Eq);
    // floor sandwich
    REQUIRE(ir.get(scoped[2].second).kind == Kind::Leq);
    REQUIRE(ir.get(scoped[3].second).kind == Kind::Lt);
}

TEST_CASE("ToIntDefinitionalLowerer: nonlinear to_int succeeds and flags bridge") {
    NativeTerms ir;
    SortId boolSort, intSort, realSort;
    setupBasicSorts(ir, boolSort, intSort, realSort);

    ExprId x = ir.add(TermExpr{Kind::Variable, realSort, {}, Payload(std::string("x"))});
    ExprId mul = ir.add(TermExpr{Kind::Mul, realSort, {x, x}, {}});
    ExprId toInt = ir.add(TermExpr{Kind::ToInt, intSort, {mul}, {}});
    ExprId three = ir.add(TermExpr{Kind::ConstInt, intSort, {}, Payload(int64_t(3))});
    ExprId eq = ir.add(TermExpr{Kind::Eq, boolSort, {toInt, three}, {}});
    ir.addAssertion(eq);

    ToIntDefinitionalLowerer t2i(ir);
    REQUIRE(t2i.run());
    REQUIRE(t2i.didLower());
    REQUIRE(t2i.hadNonlinearBridge());
}

TEST_CASE("ToIntDefinitionalLowerer: shared to_int(x) reuses i_t") {
    NativeTerms ir;
    SortId boolSort, intSort, realSort;
    setupBasicSorts(ir, boolSort, intSort, realSort);

    ExprId x = ir.add(TermExpr{Kind::Variable, realSort, {}, Payload(std::string("x"))});
    ExprId toInt1 = ir.add(TermExpr{Kind::ToInt, intSort, {x}, {}});
    ExprId toInt2 = ir.add(TermExpr{Kind::ToInt, intSort, {x}, {}});
    ExprId add = ir.add(TermExpr{Kind::Add, intSort, {toInt1, toInt2}, {}});
    ExprId zero = ir.add(TermExpr{Kind::ConstInt, intSort, {}, Payload(int64_t(0))});
    ExprId eq = ir.add(TermExpr{Kind::Eq, boolSort, {add, zero}, {}});
    ir.addAssertion(eq);

    ToIntDefinitionalLowerer t2i(ir);
    REQUIRE(t2i.run());
    REQUIRE(t2i.didLower());
    t2i.commit();

    // Should emit a single bridge + sandwich (3 side assertions), not two.
    auto scoped = ir.getScopedAssertions();
    REQUIRE(scoped.size() == 4);  // 1 rewritten + 3 side
}
