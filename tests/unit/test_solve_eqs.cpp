// Mechanics tests for SolveEqs (linear variable elimination). Soundness
// (verdict preservation + model reconstruction) is exercised end-to-end via
// the Solver integration tests; here we test the pass in isolation.
#include <doctest/doctest.h>
#include "ir/NativeTerms.h"
#include "frontend/preprocess/SolveEqs.h"
#include "frontend/preprocess/ModelConverter.h"
#include <functional>

using namespace xolver;

namespace {
void setupSorts(NativeTerms& ir, SortId& b, SortId& i, SortId& r) {
    b = ir.allocateSortId(); ir.registerSort(b, SortKind::Bool); ir.setBoolSortId(b);
    i = ir.allocateSortId(); ir.registerSort(i, SortKind::Int);  ir.setIntSortId(i);
    r = ir.allocateSortId(); ir.registerSort(r, SortKind::Real); ir.setRealSortId(r);
}
ExprId var(NativeTerms& ir, SortId s, const char* n) { return ir.add(TermExpr{Kind::Variable, s, {}, Payload(std::string(n))}); }
ExprId cint(NativeTerms& ir, SortId s, int64_t v) { return ir.add(TermExpr{Kind::ConstInt, s, {}, Payload(v)}); }
ExprId bin(NativeTerms& ir, Kind k, SortId s, ExprId a, ExprId b) { return ir.add(TermExpr{k, s, {a, b}, {}}); }

// True iff a Variable named `n` occurs in any current assertion.
bool varInAssertions(const NativeTerms& ir, const std::string& n) {
    std::function<bool(ExprId)> walk = [&](ExprId e) {
        const auto& node = ir.get(e);
        if (node.kind == Kind::Variable) {
            if (auto* nm = std::get_if<std::string>(&node.payload.value)) return *nm == n;
            return false;
        }
        for (ExprId c : node.children) if (walk(c)) return true;
        return false;
    };
    for (ExprId a : ir.assertions()) if (walk(a)) return true;
    return false;
}
} // namespace

TEST_CASE("SolveEqs: shared DAG traversal preserves reconstruction and UF context") {
    NativeTerms ir;
    SortId b, i, r;
    setupSorts(ir, b, i, r);
    auto x = var(ir, i, "x"), y = var(ir, i, "y");
    auto shared = y;
    for (int depth = 0; depth < 40; ++depth)
        shared = bin(ir, Kind::Add, i, shared, shared);
    ir.addAssertion(bin(ir, Kind::Eq, b, x, shared));
    ModelConverter converter;
    SolveEqs pass(ir, converter);
    REQUIRE(pass.run());
    pass.commit();
    CHECK(converter.size() == 1);
    std::unordered_map<std::string, RealValue> numbers{{"y", RealValue::fromInt(1)}};
    std::unordered_map<std::string, std::string> values{{"y", "1"}};
    REQUIRE(converter.reconstruct(numbers, values, ir));
    mpz_class expected = 1;
    expected <<= 40;
    CHECK(values.at("x") == expected.get_str());

    ir.clearAssertions();
    ir.addAssertion(bin(ir, Kind::Geq, b, shared, cint(ir, i, 0)));
    auto fsym = var(ir, i, "f");
    auto call = ir.add(TermExpr{Kind::UFApply, i, {fsym, shared}, Payload(std::string("f"))});
    ir.addAssertion(bin(ir, Kind::Eq, b, call, cint(ir, i, 0)));
    ir.addAssertion(bin(ir, Kind::Eq, b, y, cint(ir, i, 3)));
    ModelConverter guarded;
    SolveEqs guardedPass(ir, guarded);
    CHECK_FALSE(guardedPass.run());
    CHECK(guarded.size() == 0);
}

TEST_CASE("SolveEqs: does NOT eliminate a variable feeding a UF argument") {
    // (= x 1) AND (distinct (f (+ x 1)) (f 2)).  Eliminating x severs the
    // Nelson-Oppen shared term (+ x 1)/2 that congruence needs, causing a
    // false-SAT in combination logics (regression uflia_017). x must stay.
    NativeTerms ir; SortId b, i, r; setupSorts(ir, b, i, r);
    ExprId x = var(ir, i, "x");
    ExprId fsym = var(ir, i, "f");
    ExprId fApp1 = ir.add(TermExpr{Kind::UFApply, i, {fsym, bin(ir, Kind::Add, i, x, cint(ir, i, 1))},
                                   Payload(std::string("f"))});
    ExprId fApp2 = ir.add(TermExpr{Kind::UFApply, i, {fsym, cint(ir, i, 2)},
                                   Payload(std::string("f"))});
    ir.addAssertion(bin(ir, Kind::Eq, b, x, cint(ir, i, 1)));          // x = 1
    ir.addAssertion(bin(ir, Kind::Distinct, b, fApp1, fApp2));         // f(x+1) != f(2)

    ModelConverter mc;
    SolveEqs se(ir, mc);
    CHECK_FALSE(se.run());            // x is pinned (feeds f's argument)
    CHECK(mc.size() == 0);
    CHECK(varInAssertions(ir, "x")); // x still present
}

TEST_CASE("SolveEqs: does NOT eliminate a variable feeding an array Select index") {
    // (= x 1) AND (distinct (select a (+ x 1)) (select a 2)).  Same Nelson-Oppen
    // shared-term hazard as the UF case, but for array logics (QF_ALIA/AUFLIA):
    // eliminating x severs the shared index term (+ x 1)/2 that the array/EUF
    // congruence needs.  computeUnsafeVars guards Select/Store args identically
    // to UFApply; x must stay.
    NativeTerms ir; SortId b, i, r; setupSorts(ir, b, i, r);
    SortId arr = ir.allocateSortId(); ir.registerArraySort(arr, i, i);
    ExprId x = var(ir, i, "x");
    ExprId a = var(ir, arr, "a");
    ExprId sel1 = ir.add(TermExpr{Kind::Select, i, {a, bin(ir, Kind::Add, i, x, cint(ir, i, 1))}, {}});
    ExprId sel2 = ir.add(TermExpr{Kind::Select, i, {a, cint(ir, i, 2)}, {}});
    ir.addAssertion(bin(ir, Kind::Eq, b, x, cint(ir, i, 1)));    // x = 1
    ir.addAssertion(bin(ir, Kind::Distinct, b, sel1, sel2));     // a[x+1] != a[2]

    ModelConverter mc;
    SolveEqs se(ir, mc);
    CHECK_FALSE(se.run());            // x is pinned (feeds a Select index)
    CHECK(mc.size() == 0);
    CHECK(varInAssertions(ir, "x")); // x still present
}

TEST_CASE("SolveEqs: eliminates x from (and (= x (+ y 1)) (>= x 3))") {
    NativeTerms ir; SortId b, i, r; setupSorts(ir, b, i, r);
    ExprId x = var(ir, i, "x"), y = var(ir, i, "y");
    ExprId eqxy = bin(ir, Kind::Eq, b, x, bin(ir, Kind::Add, i, y, cint(ir, i, 1)));  // x = y+1
    ExprId geq  = bin(ir, Kind::Geq, b, x, cint(ir, i, 3));                            // x >= 3
    ir.addAssertion(bin(ir, Kind::And, b, eqxy, geq));

    ModelConverter mc;
    SolveEqs se(ir, mc);
    REQUIRE(se.run());
    se.commit();

    CHECK(se.eliminatedCount() == 1);
    CHECK(mc.size() == 1);
    CHECK_FALSE(varInAssertions(ir, "x"));   // x substituted out
    CHECK(varInAssertions(ir, "y"));         // y remains
}

TEST_CASE("SolveEqs: picks the bare-variable side of (= (+ y 1) x)") {
    NativeTerms ir; SortId b, i, r; setupSorts(ir, b, i, r);
    ExprId x = var(ir, i, "x"), y = var(ir, i, "y");
    ExprId eq = bin(ir, Kind::Eq, b, bin(ir, Kind::Add, i, y, cint(ir, i, 1)), x);  // (y+1) = x
    ir.addAssertion(eq);
    ir.addAssertion(bin(ir, Kind::Geq, b, x, cint(ir, i, 3)));

    ModelConverter mc;
    SolveEqs se(ir, mc);
    REQUIRE(se.run());
    CHECK(mc.size() == 1);
    se.commit();
    CHECK_FALSE(varInAssertions(ir, "x"));
}

TEST_CASE("SolveEqs: does NOT eliminate when the variable occurs in its own RHS") {
    NativeTerms ir; SortId b, i, r; setupSorts(ir, b, i, r);
    ExprId x = var(ir, i, "x");
    ir.addAssertion(bin(ir, Kind::Eq, b, x, bin(ir, Kind::Add, i, x, cint(ir, i, 1))));  // x = x+1
    ModelConverter mc;
    SolveEqs se(ir, mc);
    CHECK_FALSE(se.run());
    CHECK(mc.size() == 0);
}

TEST_CASE("SolveEqs: does NOT eliminate a non-equality assertion") {
    NativeTerms ir; SortId b, i, r; setupSorts(ir, b, i, r);
    ExprId x = var(ir, i, "x");
    ir.addAssertion(bin(ir, Kind::Geq, b, x, cint(ir, i, 3)));
    ModelConverter mc;
    SolveEqs se(ir, mc);
    CHECK_FALSE(se.run());
    CHECK(mc.size() == 0);
}

TEST_CASE("SolveEqs: does NOT eliminate into a non-reconstructable (div) term") {
    NativeTerms ir; SortId b, i, r; setupSorts(ir, b, i, r);
    ExprId x = var(ir, i, "x"), y = var(ir, i, "y");
    ExprId divt = bin(ir, Kind::Div, i, y, cint(ir, i, 2));   // y div 2 — not linear-reconstructable
    ir.addAssertion(bin(ir, Kind::Eq, b, x, divt));
    ModelConverter mc;
    SolveEqs se(ir, mc);
    CHECK_FALSE(se.run());
    CHECK(mc.size() == 0);
}

// ---------------------------------------------------------------------------
// General ±1-pivot linear elimination (setGeneralLinear / GAUSS).
// ---------------------------------------------------------------------------

TEST_CASE("SolveEqs: general linear equality is not a bare definition") {
    // (= (+ x y) 5): neither side is a bare variable, so the default bare-var
    // path leaves it untouched.
    NativeTerms ir; SortId b, i, r; setupSorts(ir, b, i, r);
    ExprId x = var(ir, i, "x"), y = var(ir, i, "y");
    ir.addAssertion(bin(ir, Kind::Eq, b, bin(ir, Kind::Add, i, x, y), cint(ir, i, 5)));
    ModelConverter mc;
    SolveEqs se(ir, mc);
    CHECK_FALSE(se.run());              // bare-var path: nothing to do
    CHECK(mc.size() == 0);
}

TEST_CASE("SolveEqs: polynomial definitions require an explicit policy and replay exactly") {
    NativeTerms ir; SortId b, i, r; setupSorts(ir, b, i, r);
    auto x = var(ir, i, "x"), y = var(ir, i, "y");
    ir.addAssertion(bin(ir, Kind::Eq, b, x, bin(ir, Kind::Mul, i, y, y)));
    ir.pushScope();
    ir.addAssertion(bin(ir, Kind::Gt, b, x, cint(ir, i, 2)));
    ModelConverter mc;
    SolveEqs linear(ir, mc);
    CHECK_FALSE(linear.run());
    CHECK(mc.empty());
    SolveEqs polynomial(ir, mc, SolveEqs::DefinitionPolicy::PolynomialInLinearPositions);
    REQUIRE(polynomial.run());
    polynomial.commit();
    REQUIRE(ir.getScopedAssertions().size() == 1);
    CHECK(ir.getScopedAssertions().front().first == 1);
    CHECK(ir.currentScopeLevel() == 1);
    CHECK_FALSE(varInAssertions(ir, "x"));
    std::unordered_map<std::string, RealValue> numbers{{"y", RealValue::fromInt(-3)}};
    std::unordered_map<std::string, std::string> values{{"y", "-3"}};
    REQUIRE(mc.reconstruct(numbers, values, ir));
    CHECK(values.at("x") == "9");
    ir.popScope();
    CHECK(ir.assertions().empty());
}

TEST_CASE("SolveEqs: polynomial substitution guards both DAG contexts and current aliases") {
    NativeTerms ir; SortId b, i, r; setupSorts(ir, b, i, r);
    auto x = var(ir, i, "x"), y = var(ir, i, "y"), z = var(ir, i, "z");
    SUBCASE("shared variable has a nonlinear use") {
        ir.addAssertion(bin(ir, Kind::Gt, b, x, cint(ir, i, 0)));
        ir.addAssertion(bin(ir, Kind::Gt, b, bin(ir, Kind::Mul, i, x, x), cint(ir, i, 2)));
        ir.addAssertion(bin(ir, Kind::Eq, b, x, bin(ir, Kind::Mul, i, y, y)));
    }
    SUBCASE("linear alias introduces a nonlinear use before the next definition") {
        ir.addAssertion(bin(ir, Kind::Eq, b, z, x));
        ir.addAssertion(bin(ir, Kind::Gt, b, bin(ir, Kind::Mul, i, z, z), cint(ir, i, 2)));
        ir.addAssertion(bin(ir, Kind::Eq, b, x, bin(ir, Kind::Mul, i, y, y)));
    }
    ModelConverter mc;
    SolveEqs pass(ir, mc, SolveEqs::DefinitionPolicy::PolynomialInLinearPositions);
    pass.run();
    pass.commit();
    CHECK(varInAssertions(ir, "x"));
    CHECK(varInAssertions(ir, "y"));
}

TEST_CASE("SolveEqs: real polynomial policy removes nonlinear uses without widening integer elimination") {
    for (bool integer : {false, true}) {
        NativeTerms ir; SortId b, i, r; setupSorts(ir, b, i, r);
        const auto sort = integer ? i : r;
        const auto x = var(ir, sort, "x"), y = var(ir, sort, "y");
        ir.addAssertion(bin(ir, Kind::Eq, b, x, bin(ir, Kind::Mul, sort, y, y)));
        ir.addAssertion(bin(ir, Kind::Gt, b, bin(ir, Kind::Mul, sort, x, x), cint(ir, sort, 4)));
        ModelConverter converter;
        SolveEqs pass(ir, converter, SolveEqs::DefinitionPolicy::PolynomialReals);
        if (integer) {
            CHECK_FALSE(pass.run());
            CHECK(converter.empty());
            CHECK(varInAssertions(ir, "x"));
        } else {
            REQUIRE(pass.run());
            pass.commit();
            CHECK_FALSE(varInAssertions(ir, "x"));
            CHECK(varInAssertions(ir, "y"));
            std::unordered_map<std::string, RealValue> numbers{{"y", RealValue::fromInt(3)}};
            std::unordered_map<std::string, std::string> values;
            REQUIRE(converter.reconstruct(numbers, values, ir));
            CHECK(numbers.at("x") == RealValue::fromInt(9));
        }
    }
}

TEST_CASE("SolveEqs: real polynomial definitions preserve shared UF arguments") {
    NativeTerms ir; SortId b, i, r; setupSorts(ir, b, i, r);
    const auto x = var(ir, r, "x"), y = var(ir, r, "y");
    ir.addAssertion(bin(ir, Kind::Eq, b, x, bin(ir, Kind::Mul, r, y, y)));
    const auto function = var(ir, r, "f");
    const auto call = ir.add(TermExpr{Kind::UFApply, r, {function, x}, Payload(std::string("f"))});
    ir.addAssertion(bin(ir, Kind::Eq, b, call, cint(ir, r, 1)));
    ModelConverter converter;
    SolveEqs pass(ir, converter, SolveEqs::DefinitionPolicy::PolynomialReals);
    CHECK_FALSE(pass.run());
    CHECK(converter.empty());
    CHECK(varInAssertions(ir, "x"));
}
