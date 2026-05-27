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
#include "frontend/preprocess/UnconditionalConstantPropagation.h"

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

TEST_CASE("UnconditionalConstantPropagation: deep nesting does not overflow") {
    // Runs UNCONDITIONALLY on the default path (Cap. 8a). A binding x=5 plus a
    // 200k-deep chain over x makes substituteRec/constantFoldRec recurse the
    // full term tree (former crash on insertion_sort / large QF_LRA).
    CoreIr ir; SortId b, i, r; setupSorts(ir, b, i, r);
    ExprId x = ir.add(CoreExpr{Kind::Variable, i, {}, Payload(std::string("x"))});
    ir.addAssertion(ir.add(CoreExpr{Kind::Eq, b,
        {x, ir.add(CoreExpr{Kind::ConstInt, i, {}, Payload(int64_t(5))})}, {}}));  // x = 5
    addDeepAssertion(ir, b, i, Kind::Add);   // (<= (+ ... x ...) 0) over a var named "x"
    UnconditionalConstantPropagation cprop(ir);
    REQUIRE(cprop.run());          // must not segfault
    CHECK_FALSE(cprop.hadContradiction());
    cprop.commit();
}

TEST_CASE("UnconditionalConstantPropagation: wide top-level And survives ir_.add realloc") {
    // substituteAssertion() held `const auto& node = ir_.get(assertion)` and then
    // iterated `node.children` while each substituteRec(child) called ir_.add(),
    // which reallocates exprs_ and dangles the reference (and its SmallVector
    // iterators) — a use-after-free SIGSEGV, NOT a stack overflow. Reproduced by
    // a wide top-level (and (= x 5) (<= (* x y0) 0) (<= (* x y1) 0) ...): each
    // conjunct substitutes x->5 and rebuilds (ir_.add), forcing a realloc mid-loop.
    constexpr int kWide = 4000;
    CoreIr ir; SortId b, i, r; setupSorts(ir, b, i, r);
    ExprId x = ir.add(CoreExpr{Kind::Variable, i, {}, Payload(std::string("x"))});
    ExprId five = ir.add(CoreExpr{Kind::ConstInt, i, {}, Payload(int64_t(5))});
    ExprId zero = ir.add(CoreExpr{Kind::ConstInt, i, {}, Payload(int64_t(0))});
    std::vector<ExprId> conj;
    conj.push_back(ir.add(CoreExpr{Kind::Eq, b, {x, five}, {}}));  // x = 5 (source of binding)
    for (int k = 0; k < kWide; ++k) {
        ExprId yk = ir.add(CoreExpr{Kind::Variable, i, {},
            Payload(std::string("y") + std::to_string(k))});
        ExprId prod = ir.add(CoreExpr{Kind::Mul, i, {x, yk}, {}});  // x * yk -> substitute -> rebuild
        conj.push_back(ir.add(CoreExpr{Kind::Leq, b, {prod, zero}, {}}));
    }
    CoreExpr bigAnd; bigAnd.kind = Kind::And; bigAnd.sort = b;
    for (ExprId c : conj) bigAnd.children.push_back(c);
    ir.addAssertion(ir.add(std::move(bigAnd)));
    UnconditionalConstantPropagation cprop(ir);
    REQUIRE(cprop.run());          // former: SIGSEGV from dangling node reference
    cprop.commit();
}
