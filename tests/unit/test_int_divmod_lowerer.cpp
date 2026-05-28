#include "expr/ir.h"
#include "frontend/preprocess/IntDivModLowerer.h"
#include "theory/core/LogicFeatureDetector.h"
#include <doctest/doctest.h>

using namespace xolver;

static bool containsKind(const CoreIr& ir, ExprId eid, Kind kind) {
    if (eid == NullExpr) return false;
    const auto& e = ir.get(eid);
    if (e.kind == kind) return true;
    for (ExprId child : e.children) {
        if (containsKind(ir, child, kind)) return true;
    }
    return false;
}

static bool containsIntDiv(const CoreIr& ir, ExprId eid) {
    if (eid == NullExpr) return false;
    const auto& e = ir.get(eid);
    if (e.kind == Kind::Div && e.sort == ir.intSortId()) return true;
    for (ExprId child : e.children) {
        if (containsIntDiv(ir, child)) return true;
    }
    return false;
}

static bool containsIntMod(const CoreIr& ir, ExprId eid) {
    if (eid == NullExpr) return false;
    const auto& e = ir.get(eid);
    if (e.kind == Kind::Mod && e.sort == ir.intSortId()) return true;
    for (ExprId child : e.children) {
        if (containsIntMod(ir, child)) return true;
    }
    return false;
}

static size_t countFreshDivModVars(const CoreIr& ir) {
    size_t count = 0;
    for (ExprId id = 0; id < ir.size(); ++id) {
        const auto& e = ir.get(id);
        if (e.kind == Kind::Variable) {
            if (auto* s = std::get_if<std::string>(&e.payload.value)) {
                if (s->find("__nlc_div_q") != std::string::npos ||
                    s->find("__nlc_mod_r") != std::string::npos) {
                    ++count;
                }
            }
        }
    }
    return count;
}

static size_t countUndefSymbols(const CoreIr& ir) {
    size_t count = 0;
    for (ExprId id = 0; id < ir.size(); ++id) {
        const auto& e = ir.get(id);
        if (e.kind == Kind::Variable) {
            if (auto* s = std::get_if<std::string>(&e.payload.value)) {
                if (s->find("__undef_div") != std::string::npos ||
                    s->find("__undef_mod") != std::string::npos) {
                    ++count;
                }
            }
        }
    }
    return count;
}

static CoreIr makeIrWithInt() {
    CoreIr ir;
    SortId boolSort = ir.allocateSortId();
    SortId intSort = ir.allocateSortId();
    ir.registerSort(boolSort, SortKind::Bool);
    ir.registerSort(intSort, SortKind::Int);
    ir.setBoolSortId(boolSort);
    ir.setIntSortId(intSort);
    return ir;
}

static ExprId mkIntVar(CoreIr& ir, const char* name) {
    return ir.add(CoreExpr{Kind::Variable, ir.intSortId(), {}, Payload(std::string(name))});
}

static ExprId mkIntConst(CoreIr& ir, int64_t v) {
    return ir.add(CoreExpr{Kind::ConstInt, ir.intSortId(), {}, Payload(v)});
}

static ExprId mkDiv(CoreIr& ir, ExprId a, ExprId b) {
    return ir.add(CoreExpr{Kind::Div, ir.intSortId(), {a, b}, Payload{}});
}

static ExprId mkMod(CoreIr& ir, ExprId a, ExprId b) {
    return ir.add(CoreExpr{Kind::Mod, ir.intSortId(), {a, b}, Payload{}});
}

static ExprId mkEq(CoreIr& ir, ExprId a, ExprId b) {
    return ir.add(CoreExpr{Kind::Eq, ir.boolSortId(), {a, b}, Payload{}});
}

static ExprId mkLe(CoreIr& ir, ExprId a, ExprId b) {
    return ir.add(CoreExpr{Kind::Leq, ir.boolSortId(), {a, b}, Payload{}});
}

// ---------------------------------------------------------------------------
// Constant divisor tests
// ---------------------------------------------------------------------------

TEST_CASE("IntDivModLowerer: constant divisor div") {
    CoreIr ir = makeIrWithInt();
    ExprId x = mkIntVar(ir, "x");
    ExprId three = mkIntConst(ir, 3);
    ExprId divExpr = mkDiv(ir, x, three);
    ExprId eq = mkEq(ir, divExpr, mkIntConst(ir, 2));
    ir.addAssertion(eq);

    IntDivModLowerer lowerer(ir);
    CHECK(lowerer.run());
    CHECK(!lowerer.unsupported());
    lowerer.commit();

    auto assertions = ir.getScopedAssertions();
    CHECK(assertions.size() == 4); // 1 original + 3 generated constraints

    // No Int Div/Mod left in any assertion
    for (const auto& [level, a] : assertions) {
        CHECK(!containsIntDiv(ir, a));
        CHECK(!containsIntMod(ir, a));
    }

    CHECK(countFreshDivModVars(ir) == 2); // q and r
}

TEST_CASE("IntDivModLowerer: constant divisor mod") {
    CoreIr ir = makeIrWithInt();
    ExprId x = mkIntVar(ir, "x");
    ExprId five = mkIntConst(ir, 5);
    ExprId modExpr = mkMod(ir, x, five);
    ExprId eq = mkEq(ir, modExpr, mkIntConst(ir, 2));
    ir.addAssertion(eq);

    IntDivModLowerer lowerer(ir);
    CHECK(lowerer.run());
    lowerer.commit();

    auto assertions = ir.getScopedAssertions();
    CHECK(assertions.size() == 4);

    for (const auto& [level, a] : assertions) {
        CHECK(!containsIntDiv(ir, a));
        CHECK(!containsIntMod(ir, a));
    }
}

TEST_CASE("IntDivModLowerer: negative constant divisor") {
    CoreIr ir = makeIrWithInt();
    ExprId x = mkIntVar(ir, "x");
    ExprId negThree = mkIntConst(ir, -3);
    ExprId modExpr = mkMod(ir, x, negThree);
    ExprId eq = mkEq(ir, modExpr, mkIntConst(ir, 1));
    ir.addAssertion(eq);

    IntDivModLowerer lowerer(ir);
    CHECK(lowerer.run());
    lowerer.commit();

    auto assertions = ir.getScopedAssertions();
    // a = -3*q + r, 0 <= r <= 2
    CHECK(assertions.size() == 4);

    for (const auto& [level, a] : assertions) {
        CHECK(!containsIntMod(ir, a));
    }
}

TEST_CASE("IntDivModLowerer: div and mod share same def") {
    CoreIr ir = makeIrWithInt();
    ExprId x = mkIntVar(ir, "x");
    ExprId four = mkIntConst(ir, 4);
    ExprId divExpr = mkDiv(ir, x, four);
    ExprId modExpr = mkMod(ir, x, four);
    ExprId eq1 = mkEq(ir, divExpr, mkIntConst(ir, 1));
    ExprId eq2 = mkEq(ir, modExpr, mkIntConst(ir, 2));
    ir.addAssertion(eq1);
    ir.addAssertion(eq2);

    IntDivModLowerer lowerer(ir);
    CHECK(lowerer.run());
    lowerer.commit();

    // One (x,4) pair -> one DivModDef -> 2 fresh vars (q, r)
    CHECK(countFreshDivModVars(ir) == 2);

    auto assertions = ir.getScopedAssertions();
    // 2 original + 3 shared constraints = 5
    CHECK(assertions.size() == 5);
}

// ---------------------------------------------------------------------------
// Variable divisor tests
// ---------------------------------------------------------------------------

TEST_CASE("IntDivModLowerer: variable divisor requires nonlinear + EUF") {
    CoreIr ir = makeIrWithInt();
    ExprId x = mkIntVar(ir, "x");
    ExprId y = mkIntVar(ir, "y");
    ExprId divExpr = mkDiv(ir, x, y);
    ExprId eq = mkEq(ir, divExpr, mkIntConst(ir, 1));
    ir.addAssertion(eq);

    IntDivModLowerer lowerer(ir);
    CHECK(lowerer.run());
    CHECK(!lowerer.unsupported());
    CHECK(lowerer.requirement().needsNonlinearInt);
    CHECK(lowerer.requirement().needsEUF);
    lowerer.commit();

    auto assertions = ir.getScopedAssertions();
    // Variable divisor emits: equation + 3 branches * 3 constraints = ~10 assertions
    CHECK(assertions.size() > 5);

    for (const auto& [level, a] : assertions) {
        CHECK(!containsIntDiv(ir, a));
    }
}

TEST_CASE("IntDivModLowerer: variable divisor mod") {
    CoreIr ir = makeIrWithInt();
    ExprId x = mkIntVar(ir, "x");
    ExprId y = mkIntVar(ir, "y");
    ExprId modExpr = mkMod(ir, x, y);
    ExprId eq = mkEq(ir, modExpr, mkIntConst(ir, 0));
    ir.addAssertion(eq);

    IntDivModLowerer lowerer(ir);
    CHECK(lowerer.run());
    CHECK(lowerer.requirement().needsNonlinearInt);
    CHECK(lowerer.requirement().needsEUF);
    lowerer.commit();

    for (const auto& [level, a] : ir.getScopedAssertions()) {
        CHECK(!containsIntMod(ir, a));
    }
}

// ---------------------------------------------------------------------------
// Zero divisor tests
// ---------------------------------------------------------------------------

TEST_CASE("IntDivModLowerer: zero constant divisor emits undef") {
    CoreIr ir = makeIrWithInt();
    ExprId x = mkIntVar(ir, "x");
    ExprId zero = mkIntConst(ir, 0);
    ExprId divExpr = mkDiv(ir, x, zero);
    ExprId eq = mkEq(ir, divExpr, mkIntConst(ir, 0));
    ir.addAssertion(eq);

    IntDivModLowerer lowerer(ir);
    CHECK(lowerer.run());
    CHECK(lowerer.requirement().needsEUF);
    CHECK(!lowerer.requirement().needsNonlinearInt);
    lowerer.commit();

    // Should have __undef_div and __undef_mod symbols
    CHECK(countUndefSymbols(ir) == 2);
}

// ---------------------------------------------------------------------------
// Scope tests
// ---------------------------------------------------------------------------

TEST_CASE("IntDivModLowerer: scopes are respected") {
    CoreIr ir = makeIrWithInt();
    ExprId x = mkIntVar(ir, "x");
    ExprId three = mkIntConst(ir, 3);
    ExprId divExpr = mkDiv(ir, x, three);
    ExprId eq = mkEq(ir, divExpr, mkIntConst(ir, 1));
    ir.addAssertion(eq, ScopeLevel{0});

    IntDivModLowerer lowerer(ir);
    CHECK(lowerer.run());
    lowerer.commit();

    auto assertions = ir.getScopedAssertions();
    CHECK(assertions.size() == 4);
    // All assertions should be at scope 0
    for (const auto& [level, a] : assertions) {
        CHECK(level == ScopeLevel{0});
    }
}

// ---------------------------------------------------------------------------
// Real division unaffected
// ---------------------------------------------------------------------------

TEST_CASE("IntDivModLowerer: real division is untouched") {
    CoreIr ir;
    SortId boolSort = ir.allocateSortId();
    SortId realSort = ir.allocateSortId();
    ir.registerSort(boolSort, SortKind::Bool);
    ir.registerSort(realSort, SortKind::Real);
    ir.setBoolSortId(boolSort);
    ir.setRealSortId(realSort);

    ExprId x = ir.add(CoreExpr{Kind::Variable, realSort, {}, Payload(std::string("x"))});
    ExprId two = ir.add(CoreExpr{Kind::ConstReal, realSort, {}, Payload(std::string("2.0"))});
    ExprId divExpr = ir.add(CoreExpr{Kind::Div, realSort, {x, two}, Payload{}});
    ExprId eq = ir.add(CoreExpr{Kind::Eq, boolSort, {divExpr, two}, Payload{}});
    ir.addAssertion(eq);

    IntDivModLowerer lowerer(ir);
    CHECK(lowerer.run());
    lowerer.commit();

    auto assertions = ir.getScopedAssertions();
    CHECK(assertions.size() == 1); // no constraints generated for real div

    // Real Div should still be present
    CHECK(containsKind(ir, assertions[0].second, Kind::Div));
}

// ---------------------------------------------------------------------------
// Requirement tracking
// ---------------------------------------------------------------------------

TEST_CASE("IntDivModLowerer: linear dividend + const divisor is linear") {
    CoreIr ir = makeIrWithInt();
    ExprId x = mkIntVar(ir, "x");
    ExprId three = mkIntConst(ir, 3);
    ExprId divExpr = mkDiv(ir, x, three);
    ExprId eq = mkEq(ir, divExpr, mkIntConst(ir, 1));
    ir.addAssertion(eq);

    IntDivModLowerer lowerer(ir);
    CHECK(lowerer.run());
    CHECK(!lowerer.requirement().needsNonlinearInt);
    CHECK(!lowerer.requirement().needsEUF);
}

TEST_CASE("IntDivModLowerer: nonlinear dividend + const divisor is nonlinear") {
    CoreIr ir = makeIrWithInt();
    ExprId x = mkIntVar(ir, "x");
    ExprId y = mkIntVar(ir, "y");
    ExprId xy = ir.add(CoreExpr{Kind::Mul, ir.intSortId(), {x, y}, Payload{}});
    ExprId three = mkIntConst(ir, 3);
    ExprId divExpr = mkDiv(ir, xy, three);
    ExprId eq = mkEq(ir, divExpr, mkIntConst(ir, 1));
    ir.addAssertion(eq);

    IntDivModLowerer lowerer(ir);
    CHECK(lowerer.run());
    CHECK(lowerer.requirement().needsNonlinearInt);
    CHECK(!lowerer.requirement().needsEUF);
}

TEST_CASE("IntDivModLowerer: lowering produces constraints detectable by LogicFeatureDetector") {
    CoreIr ir = makeIrWithInt();
    ExprId x = mkIntVar(ir, "x");
    ExprId three = mkIntConst(ir, 3);
    ExprId modExpr = mkMod(ir, x, three);
    ExprId eq = mkEq(ir, modExpr, mkIntConst(ir, 1));
    ir.addAssertion(eq);
    ir.addAssertion(mkLe(ir, mkIntConst(ir, 0), x));
    ir.addAssertion(mkLe(ir, x, mkIntConst(ir, 10)));

    IntDivModLowerer lowerer(ir);
    CHECK(lowerer.run());
    lowerer.commit();

    // Verify no mod left
    for (const auto& [level, a] : ir.getScopedAssertions()) {
        CHECK(!containsIntMod(ir, a));
    }

    // Verify LogicFeatureDetector does not flag unsupported
    LogicFeatureDetector detector(ir);
    LogicFeatures features = detector.detect();
    CHECK(!features.hasUnsupported);
    // 3*q is constant*var -> not nonlinear
    CHECK(!features.hasNonlinear);
    CHECK(features.hasInt);
}

TEST_CASE("IntDivModLowerer: nonlinear dividend lowering keeps hasNonlinear true for detector") {
    CoreIr ir = makeIrWithInt();
    ExprId x = mkIntVar(ir, "x");
    ExprId y = mkIntVar(ir, "y");
    ExprId xy = ir.add(CoreExpr{Kind::Mul, ir.intSortId(), {x, y}, Payload{}});
    ExprId three = mkIntConst(ir, 3);
    ExprId modExpr = mkMod(ir, xy, three);
    ExprId eq = mkEq(ir, modExpr, mkIntConst(ir, 1));
    ir.addAssertion(eq);

    IntDivModLowerer lowerer(ir);
    CHECK(lowerer.run());
    lowerer.commit();

    // Lowering replaces mod with q/r, but x*y remains in the equation:
    //   x*y = 3*q + r
    // The Mul(x,y) is still present, so detector must see nonlinear.
    LogicFeatureDetector detector(ir);
    LogicFeatures features = detector.detect();
    CHECK(!features.hasUnsupported);
    CHECK(features.hasNonlinear);
    CHECK(features.hasInt);
}
