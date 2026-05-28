// Regression test for the ToIntDefinitionalLowerer stack-overflow on deeply
// nested terms (panda sweep: ~254 crashes across NIA + IDL/LIA/RDL/LRA, all
// `ToIntDefinitionalLowerer::rewriteRec` blowing the call stack on chains
// produced by `let`-expansion of program-translation benchmarks).
//
// The pass must walk the assertion tree iteratively. With the original
// unconditional full-tree recursion this test SEGFAULTS the runner; with the
// explicit work-stack it completes. Depth is chosen well past the ~tens-of-
// thousands recursion limit of an 8MB stack (the CLI segfaults from ~100k).
#include <doctest/doctest.h>
#include "expr/ir.h"
#include "frontend/preprocess/ToIntDefinitionalLowerer.h"

using namespace xolver;

namespace {

void setupBasicSorts(CoreIr& ir, SortId& boolSort, SortId& intSort, SortId& realSort) {
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

TEST_CASE("ToIntDefinitionalLowerer: deep nesting does not overflow the stack") {
    CoreIr ir;
    SortId boolSort, intSort, realSort;
    setupBasicSorts(ir, boolSort, intSort, realSort);

    // Build a left-deep real chain  (+ (+ (+ x 1) 1) 1) ...  of depth N,
    // wrap it in (to_int chain), and assert (= (to_int chain) 3).
    const int N = 300000;
    ExprId x = ir.add(CoreExpr{Kind::Variable, realSort, {}, Payload(std::string("x"))});
    ExprId chain = x;
    for (int i = 0; i < N; ++i) {
        ExprId one = ir.add(CoreExpr{Kind::ConstReal, realSort, {}, Payload(std::string("1"))});
        chain = ir.add(CoreExpr{Kind::Add, realSort, {chain, one}, {}});
    }
    ExprId toInt = ir.add(CoreExpr{Kind::ToInt, intSort, {chain}, {}});
    ExprId three = ir.add(CoreExpr{Kind::ConstInt, intSort, {}, Payload(int64_t(3))});
    ExprId eq = ir.add(CoreExpr{Kind::Eq, boolSort, {toInt, three}, {}});
    ir.addAssertion(eq);

    ToIntDefinitionalLowerer t2i(ir);
    REQUIRE(t2i.run());          // must not segfault
    REQUIRE(t2i.didLower());     // the single to_int was lowered
    t2i.commit();

    // rewritten assertion + 3 side assertions (bridge + floor sandwich).
    auto scoped = ir.getScopedAssertions();
    REQUIRE(scoped.size() == 4);
    REQUIRE(ir.get(scoped[0].second).kind == Kind::Eq);
    REQUIRE(ir.get(scoped[1].second).kind == Kind::Eq);   // bridge r_t = chain
    REQUIRE(ir.get(scoped[2].second).kind == Kind::Leq);
    REQUIRE(ir.get(scoped[3].second).kind == Kind::Lt);
}
