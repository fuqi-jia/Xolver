#include "expr/ir.h"
#include "frontend/preprocess/RealDivLowerer.h"
#include <doctest/doctest.h>

using namespace xolver;

static bool containsRealDiv(const CoreIr& ir, ExprId eid) {
    if (eid == NullExpr) return false;
    const auto& e = ir.get(eid);
    if (e.kind == Kind::Div && e.sort == ir.realSortId()) return true;
    for (ExprId child : e.children)
        if (containsRealDiv(ir, child)) return true;
    return false;
}

static bool containsKind(const CoreIr& ir, ExprId eid, Kind k) {
    if (eid == NullExpr) return false;
    const auto& e = ir.get(eid);
    if (e.kind == k) return true;
    for (ExprId child : e.children)
        if (containsKind(ir, child, k)) return true;
    return false;
}

static size_t countDivBridgeVars(const CoreIr& ir) {
    size_t n = 0;
    for (ExprId id = 0; id < ir.size(); ++id) {
        const auto& e = ir.get(id);
        if (e.kind == Kind::Variable) {
            if (auto* s = std::get_if<std::string>(&e.payload.value))
                if (s->find("divbridge") != std::string::npos) ++n;
        }
    }
    return n;
}

static CoreIr makeRealIr() {
    CoreIr ir;
    SortId boolSort = ir.allocateSortId();
    SortId realSort = ir.allocateSortId();
    ir.registerSort(boolSort, SortKind::Bool);
    ir.registerSort(realSort, SortKind::Real);
    ir.setBoolSortId(boolSort);
    ir.setRealSortId(realSort);
    return ir;
}

static ExprId mkRealVar(CoreIr& ir, const char* n) {
    return ir.add(CoreExpr{Kind::Variable, ir.realSortId(), {}, Payload(std::string(n))});
}
static ExprId mkRealConst(CoreIr& ir, const char* s) {
    return ir.add(CoreExpr{Kind::ConstReal, ir.realSortId(), {}, Payload(std::string(s))});
}
static ExprId mkDiv(CoreIr& ir, ExprId a, ExprId b) {
    return ir.add(CoreExpr{Kind::Div, ir.realSortId(), {a, b}, Payload{}});
}
static ExprId mkLeq(CoreIr& ir, ExprId a, ExprId b) {
    return ir.add(CoreExpr{Kind::Leq, ir.boolSortId(), {a, b}, Payload{}});
}

TEST_CASE("RealDivLowerer: division by variable is purified") {
    CoreIr ir = makeRealIr();
    ExprId s = mkRealVar(ir, "s");
    ExprId b = mkRealVar(ir, "b");
    ExprId one = mkRealConst(ir, "1");
    ExprId div = mkDiv(ir, one, s);          // (/ 1 s)
    ir.addAssertion(mkLeq(ir, b, div));      // (<= b (/ 1 s))

    RealDivLowerer lowerer(ir);
    CHECK(lowerer.run());
    lowerer.commit();

    auto assertions = ir.assertions();
    // Original atom no longer contains a real division.
    for (ExprId a : assertions) CHECK(!containsRealDiv(ir, a));
    // Exactly one fresh bridge var.
    CHECK(countDivBridgeVars(ir) == 1);
    // A guarded defining constraint was emitted (Implies of a Not(=...)).
    bool hasImplies = false;
    for (ExprId a : assertions) if (containsKind(ir, a, Kind::Implies)) hasImplies = true;
    CHECK(hasImplies);
}

TEST_CASE("RealDivLowerer: division by nonzero constant is left untouched") {
    CoreIr ir = makeRealIr();
    ExprId x = mkRealVar(ir, "x");
    ExprId two = mkRealConst(ir, "2");
    ExprId div = mkDiv(ir, x, two);          // (/ x 2) — converter folds this
    ir.addAssertion(mkLeq(ir, div, x));

    RealDivLowerer lowerer(ir);
    CHECK(!lowerer.run());                    // no change
    CHECK(countDivBridgeVars(ir) == 0);
}

TEST_CASE("RealDivLowerer: identical division terms share one bridge var") {
    CoreIr ir = makeRealIr();
    ExprId a = mkRealVar(ir, "a");
    ExprId c = mkRealVar(ir, "c");
    ExprId div = mkDiv(ir, a, c);            // (/ a c) — one hash-consed ExprId
    // Use the SAME ExprId twice (mimics structural sharing).
    ir.addAssertion(mkLeq(ir, div, a));
    ir.addAssertion(mkLeq(ir, c, div));

    RealDivLowerer lowerer(ir);
    CHECK(lowerer.run());
    lowerer.commit();

    CHECK(countDivBridgeVars(ir) == 1);       // shared, not two
}

TEST_CASE("RealDivLowerer: nested division by variable purified bottom-up") {
    CoreIr ir = makeRealIr();
    ExprId a = mkRealVar(ir, "a");
    ExprId c = mkRealVar(ir, "c");
    ExprId d = mkRealVar(ir, "d");
    ExprId inner = mkDiv(ir, c, d);          // (/ c d)
    ExprId outer = mkDiv(ir, a, inner);      // (/ a (/ c d))
    ir.addAssertion(mkLeq(ir, outer, a));

    RealDivLowerer lowerer(ir);
    CHECK(lowerer.run());
    lowerer.commit();

    for (ExprId asrt : ir.assertions()) CHECK(!containsRealDiv(ir, asrt));
    CHECK(countDivBridgeVars(ir) == 2);       // one per division term
}
