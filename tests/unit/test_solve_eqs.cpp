// Mechanics tests for SolveEqs (linear variable elimination). Soundness
// (verdict preservation + model reconstruction) is exercised end-to-end via
// the Solver integration tests; here we test the pass in isolation.
#include <doctest/doctest.h>
#include "expr/ir.h"
#include "frontend/preprocess/SolveEqs.h"
#include "frontend/preprocess/ModelConverter.h"
#include <functional>

using namespace xolver;

namespace {
void setupSorts(CoreIr& ir, SortId& b, SortId& i, SortId& r) {
    b = ir.allocateSortId(); ir.registerSort(b, SortKind::Bool); ir.setBoolSortId(b);
    i = ir.allocateSortId(); ir.registerSort(i, SortKind::Int);  ir.setIntSortId(i);
    r = ir.allocateSortId(); ir.registerSort(r, SortKind::Real); ir.setRealSortId(r);
}
ExprId var(CoreIr& ir, SortId s, const char* n) { return ir.add(CoreExpr{Kind::Variable, s, {}, Payload(std::string(n))}); }
ExprId cint(CoreIr& ir, SortId s, int64_t v) { return ir.add(CoreExpr{Kind::ConstInt, s, {}, Payload(v)}); }
ExprId bin(CoreIr& ir, Kind k, SortId s, ExprId a, ExprId b) { return ir.add(CoreExpr{k, s, {a, b}, {}}); }

// True iff a Variable named `n` occurs in any current assertion.
bool varInAssertions(const CoreIr& ir, const std::string& n) {
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

TEST_CASE("SolveEqs: does NOT eliminate a variable feeding a UF argument") {
    // (= x 1) AND (distinct (f (+ x 1)) (f 2)).  Eliminating x severs the
    // Nelson-Oppen shared term (+ x 1)/2 that congruence needs, causing a
    // false-SAT in combination logics (regression uflia_017). x must stay.
    CoreIr ir; SortId b, i, r; setupSorts(ir, b, i, r);
    ExprId x = var(ir, i, "x");
    ExprId fsym = var(ir, i, "f");
    ExprId fApp1 = ir.add(CoreExpr{Kind::UFApply, i, {fsym, bin(ir, Kind::Add, i, x, cint(ir, i, 1))},
                                   Payload(std::string("f"))});
    ExprId fApp2 = ir.add(CoreExpr{Kind::UFApply, i, {fsym, cint(ir, i, 2)},
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
    CoreIr ir; SortId b, i, r; setupSorts(ir, b, i, r);
    SortId arr = ir.allocateSortId(); ir.registerSort(arr, SortKind::Array);
    ExprId x = var(ir, i, "x");
    ExprId a = var(ir, arr, "a");
    ExprId sel1 = ir.add(CoreExpr{Kind::Select, i, {a, bin(ir, Kind::Add, i, x, cint(ir, i, 1))}, {}});
    ExprId sel2 = ir.add(CoreExpr{Kind::Select, i, {a, cint(ir, i, 2)}, {}});
    ir.addAssertion(bin(ir, Kind::Eq, b, x, cint(ir, i, 1)));    // x = 1
    ir.addAssertion(bin(ir, Kind::Distinct, b, sel1, sel2));     // a[x+1] != a[2]

    ModelConverter mc;
    SolveEqs se(ir, mc);
    CHECK_FALSE(se.run());            // x is pinned (feeds a Select index)
    CHECK(mc.size() == 0);
    CHECK(varInAssertions(ir, "x")); // x still present
}

TEST_CASE("SolveEqs: eliminates x from (and (= x (+ y 1)) (>= x 3))") {
    CoreIr ir; SortId b, i, r; setupSorts(ir, b, i, r);
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
    CoreIr ir; SortId b, i, r; setupSorts(ir, b, i, r);
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
    CoreIr ir; SortId b, i, r; setupSorts(ir, b, i, r);
    ExprId x = var(ir, i, "x");
    ir.addAssertion(bin(ir, Kind::Eq, b, x, bin(ir, Kind::Add, i, x, cint(ir, i, 1))));  // x = x+1
    ModelConverter mc;
    SolveEqs se(ir, mc);
    CHECK_FALSE(se.run());
    CHECK(mc.size() == 0);
}

TEST_CASE("SolveEqs: does NOT eliminate a non-equality assertion") {
    CoreIr ir; SortId b, i, r; setupSorts(ir, b, i, r);
    ExprId x = var(ir, i, "x");
    ir.addAssertion(bin(ir, Kind::Geq, b, x, cint(ir, i, 3)));
    ModelConverter mc;
    SolveEqs se(ir, mc);
    CHECK_FALSE(se.run());
    CHECK(mc.size() == 0);
}

TEST_CASE("SolveEqs: does NOT eliminate into a non-reconstructable (div) term") {
    CoreIr ir; SortId b, i, r; setupSorts(ir, b, i, r);
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

TEST_CASE("SolveEqs[gauss]: general linear eq is NOT eliminated without the flag") {
    // (= (+ x y) 5): neither side is a bare variable, so the default bare-var
    // path leaves it untouched.
    CoreIr ir; SortId b, i, r; setupSorts(ir, b, i, r);
    ExprId x = var(ir, i, "x"), y = var(ir, i, "y");
    ir.addAssertion(bin(ir, Kind::Eq, b, bin(ir, Kind::Add, i, x, y), cint(ir, i, 5)));
    ModelConverter mc;
    SolveEqs se(ir, mc);
    CHECK_FALSE(se.run());              // bare-var path: nothing to do
    CHECK(mc.size() == 0);
}

TEST_CASE("SolveEqs[gauss]: eliminates a ±1-coefficient variable from a general eq") {
    // (= (+ x y) 5) AND (>= x 0). With GAUSS, x (coeff +1) is isolated:
    // x = 5 - y. x disappears; y remains.
    CoreIr ir; SortId b, i, r; setupSorts(ir, b, i, r);
    ExprId x = var(ir, i, "x"), y = var(ir, i, "y");
    ir.addAssertion(bin(ir, Kind::Eq, b, bin(ir, Kind::Add, i, x, y), cint(ir, i, 5)));
    ir.addAssertion(bin(ir, Kind::Geq, b, x, cint(ir, i, 0)));
    ModelConverter mc;
    SolveEqs se(ir, mc);
    se.setGeneralLinear(true);
    CHECK(se.run());
    se.commit();
    CHECK(mc.size() == 1);
    CHECK_FALSE(varInAssertions(ir, "x"));  // x eliminated
    CHECK(varInAssertions(ir, "y"));        // y remains
}

TEST_CASE("SolveEqs[gauss]: pivots on the ±1 variable, never the scaled one") {
    // (= (+ (* 2 x) y) 7) AND (>= x 0). Only y has |coeff|=1, so y is the pivot
    // (y = 7 - 2x); x (coeff 2) must NOT be eliminated — eliminating it would
    // require dividing by 2 and could drop integer solutions.
    CoreIr ir; SortId b, i, r; setupSorts(ir, b, i, r);
    ExprId x = var(ir, i, "x"), y = var(ir, i, "y");
    ExprId twoX = bin(ir, Kind::Mul, i, cint(ir, i, 2), x);
    ir.addAssertion(bin(ir, Kind::Eq, b, bin(ir, Kind::Add, i, twoX, y), cint(ir, i, 7)));
    ir.addAssertion(bin(ir, Kind::Geq, b, x, cint(ir, i, 0)));
    ModelConverter mc;
    SolveEqs se(ir, mc);
    se.setGeneralLinear(true);
    CHECK(se.run());
    se.commit();
    CHECK(mc.size() == 1);
    CHECK(varInAssertions(ir, "x"));         // scaled var stays
    CHECK_FALSE(varInAssertions(ir, "y"));   // ±1 var eliminated
}

TEST_CASE("SolveEqs[gauss]: no ±1 coefficient ⇒ no elimination") {
    // (= (+ (* 2 x) (* 3 y)) 6): every coefficient has magnitude > 1, so there
    // is no integer-exact pivot. Refuse (avoid introducing division).
    CoreIr ir; SortId b, i, r; setupSorts(ir, b, i, r);
    ExprId x = var(ir, i, "x"), y = var(ir, i, "y");
    ExprId twoX = bin(ir, Kind::Mul, i, cint(ir, i, 2), x);
    ExprId threeY = bin(ir, Kind::Mul, i, cint(ir, i, 3), y);
    ir.addAssertion(bin(ir, Kind::Eq, b, bin(ir, Kind::Add, i, twoX, threeY), cint(ir, i, 6)));
    ModelConverter mc;
    SolveEqs se(ir, mc);
    se.setGeneralLinear(true);
    CHECK_FALSE(se.run());
    CHECK(mc.size() == 0);
}

TEST_CASE("SolveEqs[gauss]: skips a UF-shared ±1 var, picks a safe one") {
    // (= (+ x y) 5) AND (distinct (f x) (f 2)). x feeds f's argument (N-O shared,
    // unsafe). GAUSS must skip x and pivot on the safe y instead.
    CoreIr ir; SortId b, i, r; setupSorts(ir, b, i, r);
    ExprId x = var(ir, i, "x"), y = var(ir, i, "y");
    ExprId fsym = var(ir, i, "f");
    ExprId fX = ir.add(CoreExpr{Kind::UFApply, i, {fsym, x}, Payload(std::string("f"))});
    ExprId f2 = ir.add(CoreExpr{Kind::UFApply, i, {fsym, cint(ir, i, 2)}, Payload(std::string("f"))});
    ir.addAssertion(bin(ir, Kind::Eq, b, bin(ir, Kind::Add, i, x, y), cint(ir, i, 5)));
    ir.addAssertion(bin(ir, Kind::Distinct, b, fX, f2));
    ModelConverter mc;
    SolveEqs se(ir, mc);
    se.setGeneralLinear(true);
    CHECK(se.run());
    se.commit();
    CHECK(mc.size() == 1);
    CHECK(varInAssertions(ir, "x"));         // UF-shared var pinned
    CHECK_FALSE(varInAssertions(ir, "y"));   // safe var eliminated
}
