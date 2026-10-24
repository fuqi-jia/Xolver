#include "ir/NativeTerms.h"
#include "frontend/preprocess/IntDivModLowerer.h"
#include "contracts/LogicFeatureDetector.h"
#include <doctest/doctest.h>

using namespace xolver;

static bool containsKind(const NativeTerms& ir, ExprId eid, Kind kind) {
    if (eid == NullExpr) return false;
    const auto& e = ir.get(eid);
    if (e.kind == kind) return true;
    for (ExprId child : e.children) {
        if (containsKind(ir, child, kind)) return true;
    }
    return false;
}

static bool containsIntDiv(const NativeTerms& ir, ExprId eid) {
    if (eid == NullExpr) return false;
    const auto& e = ir.get(eid);
    if (e.kind == Kind::Div && e.sort == ir.intSortId()) return true;
    for (ExprId child : e.children) {
        if (containsIntDiv(ir, child)) return true;
    }
    return false;
}

static bool containsIntMod(const NativeTerms& ir, ExprId eid) {
    if (eid == NullExpr) return false;
    const auto& e = ir.get(eid);
    if (e.kind == Kind::Mod && e.sort == ir.intSortId()) return true;
    for (ExprId child : e.children) {
        if (containsIntMod(ir, child)) return true;
    }
    return false;
}

static size_t countFreshDivModVars(const NativeTerms& ir) {
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

static size_t countUndefSymbols(const NativeTerms& ir) {
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

static NativeTerms makeIrWithInt() {
    NativeTerms ir;
    SortId boolSort = ir.allocateSortId();
    SortId intSort = ir.allocateSortId();
    ir.registerSort(boolSort, SortKind::Bool);
    ir.registerSort(intSort, SortKind::Int);
    ir.setBoolSortId(boolSort);
    ir.setIntSortId(intSort);
    return ir;
}

static ExprId mkIntVar(NativeTerms& ir, const char* name) {
    return ir.add(TermExpr{Kind::Variable, ir.intSortId(), {}, Payload(std::string(name))});
}

static ExprId mkIntConst(NativeTerms& ir, int64_t v) {
    return ir.add(TermExpr{Kind::ConstInt, ir.intSortId(), {}, Payload(v)});
}

static ExprId mkDiv(NativeTerms& ir, ExprId a, ExprId b) {
    return ir.add(TermExpr{Kind::Div, ir.intSortId(), {a, b}, Payload{}});
}

static ExprId mkMod(NativeTerms& ir, ExprId a, ExprId b) {
    return ir.add(TermExpr{Kind::Mod, ir.intSortId(), {a, b}, Payload{}});
}

static ExprId mkEq(NativeTerms& ir, ExprId a, ExprId b) {
    return ir.add(TermExpr{Kind::Eq, ir.boolSortId(), {a, b}, Payload{}});
}

static ExprId mkLe(NativeTerms& ir, ExprId a, ExprId b) {
    return ir.add(TermExpr{Kind::Leq, ir.boolSortId(), {a, b}, Payload{}});
}

// ---------------------------------------------------------------------------
// Constant divisor tests
// ---------------------------------------------------------------------------

TEST_CASE("IntDivModLowerer: constant divisor div") {
    NativeTerms ir = makeIrWithInt();
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
    NativeTerms ir = makeIrWithInt();
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
    NativeTerms ir = makeIrWithInt();
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
    NativeTerms ir = makeIrWithInt();
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
    NativeTerms ir = makeIrWithInt();
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

TEST_CASE("IntDivModLowerer: nonzero elimination respects polarity and scope") {
    for (auto kind : {Kind::Eq, Kind::Distinct, Kind::Geq, Kind::Gt, Kind::Leq, Kind::Lt})
        for (int value = -2; value <= 2; ++value)
            for (bool reverse : {false, true})
                for (bool negate : {false, true}) {
                    NativeTerms ir = makeIrWithInt();
                    auto x = mkIntVar(ir, "x"), d = mkIntVar(ir, "d");
                    auto number = mkIntConst(ir, value);
                    auto fact = ir.add(TermExpr{kind,
                                                ir.boolSortId(),
                                                {reverse ? number : d, reverse ? d : number},
                                                Payload{}});
                    if (negate)
                        fact = ir.add(TermExpr{Kind::Not, ir.boolSortId(), {fact}, Payload{}});
                    ir.addAssertion(fact);
                    ir.addAssertion(mkEq(ir, mkDiv(ir, x, d), mkIntConst(ir, 1)));
                    int lhs = reverse ? value : 0, rhs = reverse ? 0 : value;
                    bool atZero = kind == Kind::Eq         ? lhs == rhs
                                  : kind == Kind::Distinct ? lhs != rhs
                                  : kind == Kind::Geq      ? lhs >= rhs
                                  : kind == Kind::Gt       ? lhs > rhs
                                  : kind == Kind::Leq      ? lhs <= rhs
                                                           : lhs < rhs;
                    if (negate)
                        atZero = !atZero;
                    IntDivModLowerer lowerer(ir);
                    REQUIRE(lowerer.run());
                    CHECK(lowerer.requirement().needsEUF == atZero);
                }
    NativeTerms ir = makeIrWithInt();
    auto x = mkIntVar(ir, "x"), d = mkIntVar(ir, "d");
    auto positive = ir.add(TermExpr{Kind::Gt, ir.boolSortId(), {d, mkIntConst(ir, 0)}, Payload{}});
    auto optional =
        ir.add(TermExpr{Kind::Or, ir.boolSortId(), {positive, mkEq(ir, x, x)}, Payload{}});
    ir.addAssertion(optional);
    ir.addAssertion(mkEq(ir, mkDiv(ir, x, d), mkIntConst(ir, 1)));
    IntDivModLowerer lowerer(ir);
    REQUIRE(lowerer.run());
    CHECK(lowerer.requirement().needsEUF);
    auto division = mkEq(ir, mkDiv(ir, x, d), mkIntConst(ir, 1));
    ir.clearAssertions();
    ir.addAssertion(positive, ScopeLevel{1});
    ir.addAssertion(division, ScopeLevel{0});
    REQUIRE(lowerer.run());
    CHECK(lowerer.requirement().needsEUF);
    ir.clearAssertions();
    ir.addAssertion(positive, ScopeLevel{0});
    ir.addAssertion(division, ScopeLevel{1});
    REQUIRE(lowerer.run());
    CHECK_FALSE(lowerer.requirement().needsEUF);
}

TEST_CASE("IntDivModLowerer: variable divisor mod") {
    NativeTerms ir = makeIrWithInt();
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

TEST_CASE("IntDivModLowerer: arbitrary precision integer divisors remain linear") {
    for (const auto& text : {"18446744073709551616", "-18446744073709551616"}) {
        NativeTerms ir = makeIrWithInt();
        auto x = mkIntVar(ir, "x");
        auto divisor = ir.add(TermExpr{Kind::ConstInt, ir.intSortId(), {}, Payload(std::string(text))});
        ir.addAssertion(mkEq(ir, mkDiv(ir, x, divisor), mkIntConst(ir, 1)));
        IntDivModLowerer lowerer(ir);
        REQUIRE(lowerer.run());
        CHECK_FALSE(lowerer.requirement().needsEUF);
        CHECK_FALSE(lowerer.requirement().needsNonlinearInt);
    }
}

TEST_CASE("IntDivModLowerer: finite divisor alternatives have an exact linear encoding") {
    for (bool zeroAllowed : {false, true}) {
        NativeTerms ir = makeIrWithInt();
        auto x = mkIntVar(ir, "x"), d = mkIntVar(ir, "d");
        auto first = mkEq(ir, d, mkIntConst(ir, zeroAllowed ? 0 : 2));
        auto second = mkEq(ir, d, mkIntConst(ir, -3));
        auto domain = ir.add(TermExpr{Kind::Or, ir.boolSortId(), {first, second}, Payload{}});
        auto equation = mkEq(ir, mkMod(ir, x, d), mkIntConst(ir, 1));
        ir.addAssertion(domain);
        ir.addAssertion(equation);
        IntDivModLowerer lowerer(ir);
        REQUIRE(lowerer.run());
        CHECK_FALSE(lowerer.requirement().needsNonlinearInt);
        CHECK(lowerer.requirement().needsEUF == zeroAllowed);
        ir.clearAssertions();
        ir.addAssertion(domain, ScopeLevel{1});
        ir.addAssertion(equation, ScopeLevel{0});
        REQUIRE(lowerer.run());
        CHECK(lowerer.requirement().needsNonlinearInt);
        ir.clearAssertions();
        ir.addAssertion(domain, ScopeLevel{0});
        ir.addAssertion(equation, ScopeLevel{1});
        REQUIRE(lowerer.run());
        CHECK_FALSE(lowerer.requirement().needsNonlinearInt);

        auto other = mkIntVar(ir, "other");
        auto mixed = ir.add(TermExpr{Kind::Or, ir.boolSortId(),
            {first, mkEq(ir, other, mkIntConst(ir, 1))}, Payload{}});
        ir.clearAssertions(); ir.addAssertion(mixed); ir.addAssertion(equation);
        REQUIRE(lowerer.run());
        CHECK(lowerer.requirement().needsNonlinearInt);
    }
}

// ---------------------------------------------------------------------------
// Zero divisor tests
// ---------------------------------------------------------------------------

TEST_CASE("IntDivModLowerer: zero constant divisor emits undef") {
    NativeTerms ir = makeIrWithInt();
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
    NativeTerms ir = makeIrWithInt();
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
    NativeTerms ir;
    SortId boolSort = ir.allocateSortId();
    SortId realSort = ir.allocateSortId();
    ir.registerSort(boolSort, SortKind::Bool);
    ir.registerSort(realSort, SortKind::Real);
    ir.setBoolSortId(boolSort);
    ir.setRealSortId(realSort);

    ExprId x = ir.add(TermExpr{Kind::Variable, realSort, {}, Payload(std::string("x"))});
    ExprId two = ir.add(TermExpr{Kind::ConstReal, realSort, {}, Payload(std::string("2.0"))});
    ExprId divExpr = ir.add(TermExpr{Kind::Div, realSort, {x, two}, Payload{}});
    ExprId eq = ir.add(TermExpr{Kind::Eq, boolSort, {divExpr, two}, Payload{}});
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
    NativeTerms ir = makeIrWithInt();
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
    NativeTerms ir = makeIrWithInt();
    ExprId x = mkIntVar(ir, "x");
    ExprId y = mkIntVar(ir, "y");
    ExprId xy = ir.add(TermExpr{Kind::Mul, ir.intSortId(), {x, y}, Payload{}});
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
    NativeTerms ir = makeIrWithInt();
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
    NativeTerms ir = makeIrWithInt();
    ExprId x = mkIntVar(ir, "x");
    ExprId y = mkIntVar(ir, "y");
    ExprId xy = ir.add(TermExpr{Kind::Mul, ir.intSortId(), {x, y}, Payload{}});
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
