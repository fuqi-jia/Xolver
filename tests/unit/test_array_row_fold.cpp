// Mechanics tests for ArrayReadOverWrite (constant-index read-over-write
// store-chain folding). Soundness (verdict preservation) is exercised
// end-to-end via the Solver integration tests; here we test the pass in
// isolation. The pass resolves `(select (store* base ...) c)` for a constant
// read index `c` by walking the store chain once (the read-over-write axiom on
// decidable constant indices), stopping at any variable-index store it cannot
// safely skip.
#include <doctest/doctest.h>
#include "expr/ir.h"
#include "frontend/preprocess/ArrayReadOverWrite.h"

using namespace xolver;

namespace {
void setupSorts(CoreIr& ir, SortId& b, SortId& i, SortId& r, SortId& arr) {
    b = ir.allocateSortId(); ir.registerSort(b, SortKind::Bool); ir.setBoolSortId(b);
    i = ir.allocateSortId(); ir.registerSort(i, SortKind::Int);  ir.setIntSortId(i);
    r = ir.allocateSortId(); ir.registerSort(r, SortKind::Real); ir.setRealSortId(r);
    arr = ir.allocateSortId(); ir.registerSort(arr, SortKind::Array);
}
ExprId var(CoreIr& ir, SortId s, const char* n) { return ir.add(CoreExpr{Kind::Variable, s, {}, Payload(std::string(n))}); }
ExprId cint(CoreIr& ir, SortId s, int64_t v) { return ir.add(CoreExpr{Kind::ConstInt, s, {}, Payload(v)}); }
ExprId store(CoreIr& ir, SortId arr, ExprId a, ExprId idx, ExprId v) { return ir.add(CoreExpr{Kind::Store, arr, {a, idx, v}, {}}); }
ExprId select(CoreIr& ir, SortId s, ExprId a, ExprId idx) { return ir.add(CoreExpr{Kind::Select, s, {a, idx}, {}}); }
ExprId eq(CoreIr& ir, SortId b, ExprId a, ExprId c) { return ir.add(CoreExpr{Kind::Eq, b, {a, c}, {}}); }

// The (single) assertion's RHS after the pass (assertions are `(= y <expr>)`).
ExprId rhs(const CoreIr& ir) {
    const auto& as = ir.getScopedAssertions();
    REQUIRE(as.size() == 1);
    const auto& n = ir.get(as[0].second);
    REQUIRE(n.kind == Kind::Eq);
    REQUIRE(n.children.size() == 2);
    return n.children[1];
}
bool isConstInt(const CoreIr& ir, ExprId e, int64_t v) {
    const auto& n = ir.get(e);
    if (n.kind != Kind::ConstInt) return false;
    auto* p = std::get_if<int64_t>(&n.payload.value);
    return p && *p == v;
}
} // namespace

TEST_CASE("ROW-fold: constant chain resolves to the most-recent matching value") {
    // (select (store (store a 0 5) 1 7) 0) -> 5  (top store is idx 1 != 0, skip;
    // next store is idx 0 == 0, hit -> value 5).
    CoreIr ir; SortId b, i, r, arr; setupSorts(ir, b, i, r, arr);
    ExprId a = var(ir, arr, "a"), y = var(ir, i, "y");
    ExprId chain = store(ir, arr, store(ir, arr, a, cint(ir, i, 0), cint(ir, i, 5)),
                         cint(ir, i, 1), cint(ir, i, 7));
    ir.addAssertion(eq(ir, b, y, select(ir, i, chain, cint(ir, i, 0))));

    ArrayReadOverWrite pass(ir);
    CHECK(pass.run());
    pass.commit();
    CHECK(isConstInt(ir, rhs(ir), 5));
}

TEST_CASE("ROW-fold: hit at top of chain") {
    // (select (store a 0 9) 0) -> 9
    CoreIr ir; SortId b, i, r, arr; setupSorts(ir, b, i, r, arr);
    ExprId a = var(ir, arr, "a"), y = var(ir, i, "y");
    ExprId chain = store(ir, arr, a, cint(ir, i, 0), cint(ir, i, 9));
    ir.addAssertion(eq(ir, b, y, select(ir, i, chain, cint(ir, i, 0))));

    ArrayReadOverWrite pass(ir);
    CHECK(pass.run());
    pass.commit();
    CHECK(isConstInt(ir, rhs(ir), 9));
}

TEST_CASE("ROW-fold: peels a non-matching constant store, leaving residual select") {
    // (select (store a 1 7) 0) -> (select a 0)  (0 != 1: peel; base var a remains).
    CoreIr ir; SortId b, i, r, arr; setupSorts(ir, b, i, r, arr);
    ExprId a = var(ir, arr, "a"), y = var(ir, i, "y");
    ExprId chain = store(ir, arr, a, cint(ir, i, 1), cint(ir, i, 7));
    ir.addAssertion(eq(ir, b, y, select(ir, i, chain, cint(ir, i, 0))));

    ArrayReadOverWrite pass(ir);
    CHECK(pass.run());
    pass.commit();
    ExprId res = rhs(ir);
    const auto& n = ir.get(res);
    REQUIRE(n.kind == Kind::Select);
    REQUIRE(n.children.size() == 2);
    CHECK(n.children[0] == a);                 // base var, store peeled away
    CHECK(isConstInt(ir, n.children[1], 0));   // index unchanged
}

TEST_CASE("ROW-fold: variable store index blocks the walk (sound: cannot skip)") {
    // (select (store a z 7) 0) with z a variable -> unchanged (z might alias 0).
    CoreIr ir; SortId b, i, r, arr; setupSorts(ir, b, i, r, arr);
    ExprId a = var(ir, arr, "a"), y = var(ir, i, "y"), z = var(ir, i, "z");
    ExprId chain = store(ir, arr, a, z, cint(ir, i, 7));
    ExprId sel = select(ir, i, chain, cint(ir, i, 0));
    ir.addAssertion(eq(ir, b, y, sel));

    ArrayReadOverWrite pass(ir);
    bool changed = pass.run();
    pass.commit();
    CHECK_FALSE(changed);            // nothing safely resolvable
    CHECK(rhs(ir) == sel);           // structurally identical
}

TEST_CASE("ROW-fold: read past a non-matching const store but stop at a variable store") {
    // (select (store (store a z 1) 2 8) 0):
    //   top store idx 2 != 0 -> peel; next store idx z (variable) -> stop.
    //   residual: (select (store a z 1) 0).
    CoreIr ir; SortId b, i, r, arr; setupSorts(ir, b, i, r, arr);
    ExprId a = var(ir, arr, "a"), y = var(ir, i, "y"), z = var(ir, i, "z");
    ExprId inner = store(ir, arr, a, z, cint(ir, i, 1));
    ExprId chain = store(ir, arr, inner, cint(ir, i, 2), cint(ir, i, 8));
    ir.addAssertion(eq(ir, b, y, select(ir, i, chain, cint(ir, i, 0))));

    ArrayReadOverWrite pass(ir);
    CHECK(pass.run());
    pass.commit();
    ExprId res = rhs(ir);
    const auto& n = ir.get(res);
    REQUIRE(n.kind == Kind::Select);
    CHECK(n.children[0] == inner);             // peeled the idx-2 store, kept idx-z store
    CHECK(isConstInt(ir, n.children[1], 0));
}

TEST_CASE("ROW-fold: nested-array select over a base variable is untouched") {
    // (select (select status 1) 0): inner reads an array out of an array-of-array
    // base variable -> not a store chain -> both selects left intact.
    CoreIr ir; SortId b, i, r, arr; setupSorts(ir, b, i, r, arr);
    SortId arr2 = ir.allocateSortId(); ir.registerSort(arr2, SortKind::Array);
    ExprId status = var(ir, arr2, "status"), y = var(ir, i, "y");
    ExprId inner = select(ir, arr, status, cint(ir, i, 1));   // array-valued
    ExprId outer = select(ir, i, inner, cint(ir, i, 0));
    ir.addAssertion(eq(ir, b, y, outer));

    ArrayReadOverWrite pass(ir);
    bool changed = pass.run();
    pass.commit();
    CHECK_FALSE(changed);
    CHECK(rhs(ir) == outer);
}
