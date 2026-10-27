// Replay-correctness tests for ModelConverter (reconstruction of variables
// eliminated by solve-eqs). The reconstructed model must give eliminated vars
// the value of their defining term under the rest of the model.
#include <doctest/doctest.h>
#include "ir/NativeTerms.h"
#include "frontend/preprocess/ModelConverter.h"
#include "base/RealValue.h"
#include "base/EnvParam.h"
#include "xolver/Solver.h"

using namespace xolver;

namespace {
void setupSorts(NativeTerms& ir, SortId& b, SortId& i, SortId& r) {
    b = ir.allocateSortId(); ir.registerSort(b, SortKind::Bool); ir.setBoolSortId(b);
    i = ir.allocateSortId(); ir.registerSort(i, SortKind::Int);  ir.setIntSortId(i);
    r = ir.allocateSortId(); ir.registerSort(r, SortKind::Real); ir.setRealSortId(r);
}
ExprId var(NativeTerms& ir, SortId s, const char* n) {
    return ir.add(TermExpr{Kind::Variable, s, {}, Payload(std::string(n))});
}
ExprId cint(NativeTerms& ir, SortId s, int64_t v) {
    return ir.add(TermExpr{Kind::ConstInt, s, {}, Payload(v)});
}
ExprId add(NativeTerms& ir, SortId s, ExprId a, ExprId b) {
    return ir.add(TermExpr{Kind::Add, s, {a, b}, {}});
}
} // namespace

TEST_CASE("ModelConverter: reconstructs x = y + 1 from the model of y") {
    NativeTerms ir; SortId b, i, r; setupSorts(ir, b, i, r);
    ExprId t = add(ir, i, var(ir, i, "y"), cint(ir, i, 1));   // y + 1

    ModelConverter mc;
    mc.registerElimination("x", i, t);

    std::unordered_map<std::string, RealValue> numAsg;
    std::unordered_map<std::string, std::string> strAsg;
    numAsg["y"] = RealValue::fromInt(4);

    REQUIRE(mc.reconstruct(numAsg, strAsg, ir));
    REQUIRE(numAsg.count("x") == 1);
    CHECK(numAsg["x"] == RealValue::fromInt(5));
    CHECK(strAsg["x"] == "5");   // string channel (modelMatchesOriginal/dumpModel)
}

TEST_CASE("ModelConverter: reverse-order replay resolves chained eliminations") {
    // Eliminated in order:  x = y + 1   (registered first),
    //                       y = z + 2   (registered second).
    // Over {z = 10}, reverse replay must give y = 12 then x = 13.
    NativeTerms ir; SortId b, i, r; setupSorts(ir, b, i, r);
    ExprId tx = add(ir, i, var(ir, i, "y"), cint(ir, i, 1));   // y + 1
    ExprId ty = add(ir, i, var(ir, i, "z"), cint(ir, i, 2));   // z + 2

    ModelConverter mc;
    mc.registerElimination("x", i, tx);
    mc.registerElimination("y", i, ty);

    std::unordered_map<std::string, RealValue> numAsg;
    std::unordered_map<std::string, std::string> strAsg;
    numAsg["z"] = RealValue::fromInt(10);

    REQUIRE(mc.reconstruct(numAsg, strAsg, ir));
    CHECK(numAsg["y"] == RealValue::fromInt(12));
    CHECK(numAsg["x"] == RealValue::fromInt(13));
}

TEST_CASE("ModelConverter: missing dependency leaves reconstruct() false") {
    // x = w + 1 but w is not in the model and not eliminated -> cannot rebuild.
    // STRICT Elim path (SolveEqs): a missing free var is a solver bug, so
    // reconstruct() must fail loudly rather than invent a value (a39f26c).
    NativeTerms ir; SortId b, i, r; setupSorts(ir, b, i, r);
    ExprId t = add(ir, i, var(ir, i, "w"), cint(ir, i, 1));

    ModelConverter mc;
    mc.registerElimination("x", i, t);

    std::unordered_map<std::string, RealValue> numAsg;  // empty
    std::unordered_map<std::string, std::string> strAsg;
    CHECK_FALSE(mc.reconstruct(numAsg, strAsg, ir));
}

TEST_CASE("ModelConverter: affine algebraic replay resolves chains and replaces defaults") {
    NativeTerms ir; SortId b, i, r; setupSorts(ir, b, i, r);
    const auto y = var(ir, r, "y"), z = var(ir, r, "z");
    const auto half = ir.add(TermExpr{Kind::ConstReal, r, {}, Payload(std::string("1/2"))});
    const auto halfY = ir.add(TermExpr{Kind::Mul, r, {half, y}, {}});
    const auto twiceZ = ir.add(TermExpr{Kind::Mul, r, {cint(ir, r, 2), z}, {}});
    ModelConverter mc;
    mc.registerElimination("x", r, add(ir, r, halfY, cint(ir, r, 1)));
    mc.registerElimination("y", r, add(ir, r, twiceZ, cint(ir, r, -3)));
    const auto root = RealValue::fromAlgebraic(
        AlgebraicNumber{{mpz_class(-2), mpz_class(0), mpz_class(1)}, 1, 2});
    std::unordered_map<std::string, RealValue> numbers{{"z", root}, {"y", RealValue::fromInt(0)}};
    // Typed values take precedence; an old rational y must not remain in the
    // rational environment after replay reconstructs an algebraic y.
    std::unordered_map<std::string, std::string> strings{{"z", "0"}, {"y", "0"}};
    REQUIRE(mc.reconstruct(numbers, strings, ir));
    const auto shiftedX = numbers.at("x") + RealValue::fromMpq(mpq_class(1, 2));
    const auto shiftedY = numbers.at("y") + RealValue::fromInt(3);
    CHECK(shiftedX.sign() > 0);
    CHECK(shiftedX * shiftedX == RealValue::fromInt(2));
    CHECK(shiftedY.sign() > 0);
    CHECK(shiftedY * shiftedY == RealValue::fromInt(8));
    CHECK(strings.at("x").find("root-of-with-interval") != std::string::npos);
    CHECK(strings.at("y").find("root-of-with-interval") != std::string::npos);
}

TEST_CASE("ModelConverter: algebraic cancellation and unsupported dependencies remain exact") {
    NativeTerms ir; SortId b, i, r; setupSorts(ir, b, i, r);
    const auto z = var(ir, r, "z"), missing = var(ir, r, "missing");
    const auto difference = ir.add(TermExpr{Kind::Sub, r, {z, z}, {}});
    const auto root = RealValue::fromAlgebraic(
        AlgebraicNumber{{mpz_class(-2), mpz_class(0), mpz_class(1)}, 1, 2});
    std::unordered_map<std::string, RealValue> numbers{{"z", root}};
    std::unordered_map<std::string, std::string> strings;
    ModelConverter mc;
    SUBCASE("correlated roots cancel to a rational") {
        mc.registerElimination("x", r, difference);
        REQUIRE(mc.reconstruct(numbers, strings, ir));
        CHECK(numbers.at("x").isRational());
        CHECK(numbers.at("x") == RealValue::fromInt(0));
        CHECK(strings.at("x") == "0");
    }
    SUBCASE("cancelled missing dependencies still fail the strict contract") {
        const auto cancelled = ir.add(TermExpr{Kind::Sub, r, {missing, missing}, {}});
        mc.registerElimination("x", r, add(ir, r, difference, cancelled));
        CHECK_FALSE(mc.reconstruct(numbers, strings, ir));
        CHECK_FALSE(numbers.count("x"));
    }
    SUBCASE("polynomial algebraic definitions replay exactly") {
        mc.registerElimination("x", r, ir.add(TermExpr{Kind::Mul, r, {z, z}, {}}));
        REQUIRE(mc.reconstruct(numbers, strings, ir));
        CHECK(numbers.at("x") == RealValue::fromInt(2));
        CHECK(numbers.at("x").isExactInteger());
    }
    SUBCASE("non-polynomial algebraic definitions remain unsupported") {
        mc.registerElimination("x", r, ir.add(TermExpr{Kind::Div, r, {z, z}, {}}));
        CHECK_FALSE(mc.reconstruct(numbers, strings, ir));
        CHECK_FALSE(numbers.count("x"));
    }
    SUBCASE("polynomial cancellation cannot hide a missing dependency") {
        const auto square = ir.add(TermExpr{Kind::Mul, r, {z, z}, {}});
        const auto cancelled = ir.add(TermExpr{Kind::Sub, r, {missing, missing}, {}});
        mc.registerElimination("x", r, add(ir, r, square, cancelled));
        CHECK_FALSE(mc.reconstruct(numbers, strings, ir));
        CHECK_FALSE(numbers.count("x"));
    }
    SUBCASE("an irrational value cannot reconstruct an integer") {
        mc.registerElimination("x", i, z);
        CHECK_FALSE(mc.reconstruct(numbers, strings, ir));
        CHECK_FALSE(numbers.count("x"));
    }
}

TEST_CASE("ModelConverter: polynomial algebraic chains replace defaults and preserve identities") {
    NativeTerms ir; SortId b, i, r; setupSorts(ir, b, i, r);
    const auto y = var(ir, r, "y"), z = var(ir, r, "z");
    const auto yy = ir.add(TermExpr{Kind::Mul, r, {y, y}, {}});
    const auto zz = ir.add(TermExpr{Kind::Mul, r, {z, z}, {}});
    const auto fourY = ir.add(TermExpr{Kind::Mul, r, {cint(ir, r, 4), y}, {}});
    ModelConverter mc;
    mc.registerElimination("x", r, ir.add(TermExpr{Kind::Sub, r, {yy, fourY}, {}}));
    mc.registerElimination("y", r, add(ir, r, zz, z));
    const auto root = RealValue::fromAlgebraic(
        AlgebraicNumber{{mpz_class(-2), mpz_class(0), mpz_class(1)}, 1, 2});
    std::unordered_map<std::string, RealValue> numbers{{"z", root}, {"y", RealValue::fromInt(0)}};
    std::unordered_map<std::string, std::string> strings{{"z", "0"}, {"y", "0"}};
    REQUIRE(mc.reconstruct(numbers, strings, ir));
    const auto shifted = numbers.at("y") - RealValue::fromInt(2);
    CHECK(shifted.sign() > 0);
    CHECK(shifted * shifted == RealValue::fromInt(2));
    CHECK(numbers.at("x") == RealValue::fromInt(-2));
    CHECK(strings.at("y").find("root-of-with-interval") != std::string::npos);
}

TEST_CASE("ModelConverter: real polynomial definitions survive repeated checks and rollback") {
    Solver solver;
    solver.setLogic("QF_NRA");
    const auto x = solver.mkVar(solver.realSort(), "polynomial-x");
    const auto y = solver.mkVar(solver.realSort(), "polynomial-y");
    auto op = [&](Kind kind, std::initializer_list<Term> terms) {
        return solver.mkOp(static_cast<uint32_t>(kind), std::vector<Term>(terms));
    };
    const auto square = op(Kind::Mul, {y, y});
    solver.assertFormula(op(Kind::Eq, {square, solver.mkReal("2")}));
    solver.assertFormula(op(Kind::Gt, {y, solver.mkReal("0")}));
    solver.assertFormula(op(Kind::Eq, {x, op(Kind::Add, {square, solver.mkReal("1")})}));
    solver.assertFormula(op(Kind::Eq, {op(Kind::Mul, {x, x}), solver.mkReal("9")}));
    for (int repeat = 0; repeat < 2; ++repeat) {
        CHECK((solver.checkSat() == Result::Sat));
        CHECK(solver.getModel().getValue(x.id()) != nullptr);
        solver.push();
        solver.assertFormula(op(Kind::Lt, {x, solver.mkReal("0")}));
        CHECK((solver.checkSat() == Result::Unsat));
        solver.pop();
    }
    CHECK((solver.checkSat() == Result::Sat));
}

TEST_CASE("ModelConverter: NRA definitions survive repeated checks and rollback") {
    Solver solver;
    solver.setLogic("QF_NRA");
    const auto x = solver.mkVar(solver.realSort(), "definition-x");
    const auto y = solver.mkVar(solver.realSort(), "definition-y");
    auto op = [&](Kind kind, std::initializer_list<Term> terms) {
        return solver.mkOp(static_cast<uint32_t>(kind), std::vector<Term>(terms));
    };
    solver.assertFormula(op(Kind::Eq, {op(Kind::Mul, {y, y}), solver.mkReal("2")}));
    solver.assertFormula(op(Kind::Gt, {y, solver.mkReal("0")}));
    solver.assertFormula(op(Kind::Eq, {x, op(Kind::Add, {y, solver.mkReal("1")})}));
    for (int repeat = 0; repeat < 2; ++repeat) {
        CHECK((solver.checkSat() == Result::Sat));
        CHECK(solver.getModel().getValue(x.id()) != nullptr);
        solver.push();
        solver.assertFormula(op(Kind::Lt, {x, solver.mkReal("1")}));
        CHECK((solver.checkSat() == Result::Unsat));
        solver.pop();
    }
    CHECK((solver.checkSat() == Result::Sat));
    CHECK(solver.getModel().getValue(x.id()) != nullptr);
}

TEST_CASE("ModelConverter: NRA free affine parameters keep a complete model") {
    Solver solver;
    solver.setLogic("QF_NRA");
    const auto x = solver.mkVar(solver.realSort(), "free-x");
    const auto y = solver.mkVar(solver.realSort(), "free-y");
    const auto sum = solver.mkOp(static_cast<uint32_t>(Kind::Add), {y, solver.mkReal("1")});
    solver.assertFormula(solver.mkOp(static_cast<uint32_t>(Kind::Eq), {x, sum}));
    REQUIRE((solver.checkSat() == Result::Sat));
    CHECK(solver.getModel().getValue(x.id()) != nullptr);
    CHECK(solver.getModel().getValue(y.id()) != nullptr);
}
