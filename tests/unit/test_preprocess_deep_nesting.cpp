// Stack-overflow regression for the frontend preprocess passes that walk the
// whole term tree. All were converted from recursion to explicit work-stacks
// (panda sweep: deeply-nested let-expanded benchmarks blew the call stack).
// Each case builds a depth-200k chain and runs the pass: the former recursion
// SIGSEGV'd the runner; the iterative version completes.
#include <doctest/doctest.h>
#include "expr/ir.h"
#include "frontend/preprocess/IntDivModConstantFold.h"
#include "frontend/preprocess/ToRealLiteralFold.h"
#include "frontend/preprocess/NaryDistinctLowerer.h"
#include "frontend/preprocess/IntDivModLowerer.h"
#include "frontend/preprocess/FormulaRewriter.h"
#include "frontend/preprocess/UfInArithPurifier.h"
#include "frontend/preprocess/BoolSubtermPurifier.h"

using namespace zolver;

namespace {

constexpr int kDeep = 200000;

void setupSorts(CoreIr& ir, SortId& boolSort, SortId& intSort, SortId& realSort) {
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

// Build a left-deep chain  (op (op (op x c) c) c) ...  of the given depth,
// then assert  (<= chain 0).  Returns nothing; the assertion is registered.
void addDeepAssertion(CoreIr& ir, SortId boolSort, SortId numSort, Kind op) {
    ExprId x = ir.add(CoreExpr{Kind::Variable, numSort, {}, Payload(std::string("x"))});
    ExprId chain = x;
    for (int i = 0; i < kDeep; ++i) {
        ExprId c = (numSort == ir.intSortId())
                       ? ir.add(CoreExpr{Kind::ConstInt, numSort, {}, Payload(int64_t(1))})
                       : ir.add(CoreExpr{Kind::ConstReal, numSort, {}, Payload(std::string("1"))});
        chain = ir.add(CoreExpr{op, numSort, {chain, c}, {}});
    }
    ExprId zero = (numSort == ir.intSortId())
                      ? ir.add(CoreExpr{Kind::ConstInt, numSort, {}, Payload(int64_t(0))})
                      : ir.add(CoreExpr{Kind::ConstReal, numSort, {}, Payload(std::string("0"))});
    ir.addAssertion(ir.add(CoreExpr{Kind::Leq, boolSort, {chain, zero}, {}}));
}

} // namespace

TEST_CASE("IntDivModConstantFold: deep nesting does not overflow") {
    CoreIr ir; SortId b, i, r; setupSorts(ir, b, i, r);
    addDeepAssertion(ir, b, i, Kind::Add);
    IntDivModConstantFold pass(ir);
    REQUIRE(pass.run());
}

TEST_CASE("ToRealLiteralFold: deep nesting does not overflow") {
    CoreIr ir; SortId b, i, r; setupSorts(ir, b, i, r);
    addDeepAssertion(ir, b, r, Kind::Add);
    ToRealLiteralFold pass(ir);
    REQUIRE(pass.run());
}

TEST_CASE("NaryDistinctLowerer: deep nesting does not overflow") {
    CoreIr ir; SortId b, i, r; setupSorts(ir, b, i, r);
    addDeepAssertion(ir, b, i, Kind::Add);
    NaryDistinctLowerer pass(ir);
    REQUIRE(pass.run());
}

TEST_CASE("IntDivModLowerer: deep nesting does not overflow") {
    CoreIr ir; SortId b, i, r; setupSorts(ir, b, i, r);
    addDeepAssertion(ir, b, i, Kind::Add);
    IntDivModLowerer pass(ir);
    REQUIRE(pass.run());
}

TEST_CASE("FormulaRewriter: deep nesting does not overflow") {
    CoreIr ir; SortId b, i, r; setupSorts(ir, b, i, r);
    addDeepAssertion(ir, b, i, Kind::Add);
    FormulaRewriter pass(ir, b);
    pass.run();  // must not segfault; verdict is irrelevant here
}

TEST_CASE("UfInArithPurifier: deep nesting does not overflow") {
    CoreIr ir; SortId b, i, r; setupSorts(ir, b, i, r);
    addDeepAssertion(ir, b, i, Kind::Add);
    UfInArithPurifier pass(ir);
    pass.run();  // returns bool changed_; just must not segfault
    CHECK(true);
}

TEST_CASE("BoolSubtermPurifier: deep nesting does not overflow") {
    CoreIr ir; SortId b, i, r; setupSorts(ir, b, i, r);
    addDeepAssertion(ir, b, i, Kind::Add);
    BoolSubtermPurifier pass(ir);
    pass.run();  // returns bool changed_; just must not segfault
    CHECK(true);
}
