#include "xolver/Solver.h"
#include "ir/NativeTerms.h"
#include <doctest/doctest.h>

using namespace xolver;

TEST_CASE("IteLowerer: incremental push/pop with ITE via API") {
    Solver solver;
    solver.setLogic("QF_UF");
    Sort boolSort = solver.boolSort();

    Term c = solver.mkVar(boolSort, "c");
    Term a = solver.mkVar(boolSort, "a");
    Term b = solver.mkVar(boolSort, "b");
    Term ite_cab = solver.mkOp(static_cast<uint32_t>(Kind::Ite), {c, a, b});

    // Scenario 1: c=true, distinct(ite(c,a,b), a) -> unsat
    solver.push();
    solver.assertFormula(solver.mkOp(static_cast<uint32_t>(Kind::Eq), {c, solver.mkBool(true)}));
    solver.assertFormula(solver.mkOp(static_cast<uint32_t>(Kind::Distinct), {ite_cab, a}));
    Result r1 = solver.checkSat();
    CHECK(static_cast<int>(r1) == static_cast<int>(Result::Unsat));
    solver.pop();

    // Scenario 2: c=false, distinct(ite(c,a,b), b) -> unsat
    solver.push();
    solver.assertFormula(solver.mkOp(static_cast<uint32_t>(Kind::Eq), {c, solver.mkBool(false)}));
    solver.assertFormula(solver.mkOp(static_cast<uint32_t>(Kind::Distinct), {ite_cab, b}));
    Result r2 = solver.checkSat();
    CHECK(static_cast<int>(r2) == static_cast<int>(Result::Unsat));
    solver.pop();

    // Scenario 3: a=b, distinct(ite(c,a,b), a) -> unsat (branches equal)
    solver.push();
    solver.assertFormula(solver.mkOp(static_cast<uint32_t>(Kind::Eq), {a, b}));
    solver.assertFormula(solver.mkOp(static_cast<uint32_t>(Kind::Distinct), {ite_cab, a}));
    Result r3 = solver.checkSat();
    CHECK(static_cast<int>(r3) == static_cast<int>(Result::Unsat));
    solver.pop();

    // Scenario 4: c=true, distinct(ite(c,a,b), a) -> unsat (again)
    solver.push();
    solver.assertFormula(solver.mkOp(static_cast<uint32_t>(Kind::Eq), {c, solver.mkBool(true)}));
    solver.assertFormula(solver.mkOp(static_cast<uint32_t>(Kind::Distinct), {ite_cab, a}));
    Result r4 = solver.checkSat();
    CHECK(static_cast<int>(r4) == static_cast<int>(Result::Unsat));
    solver.pop();

    // Scenario 5: self-equality -> sat
    solver.assertFormula(solver.mkOp(static_cast<uint32_t>(Kind::Eq), {ite_cab, ite_cab}));
    Result r5 = solver.checkSat();
    CHECK(static_cast<int>(r5) == static_cast<int>(Result::Sat));
}

TEST_CASE("IteLowerer: arithmetic affine choices preserve incremental branch semantics") {
    for (bool real : {false, true}) {
        Solver solver;
        solver.setLogic(real ? "QF_LRA" : "QF_LIA");
        const auto sort = real ? solver.realSort() : solver.intSort();
        const auto c = solver.mkVar(solver.boolSort(), "choice");
        const auto x = solver.mkVar(sort, "value");
        auto op = [&](Kind kind, std::initializer_list<Term> terms) {
            return solver.mkOp(static_cast<uint32_t>(kind), std::vector<Term>(terms));
        };
        auto constant = [&](int value) { return real ? solver.mkReal(std::to_string(value)) : solver.mkInt(value); };
        const auto base = op(Kind::Mul, {constant(-3), x});
        const auto left = op(Kind::Add, {base, constant(-5)});
        const auto right = op(Kind::Add, {base, constant(7)});
        const auto choice = op(Kind::Ite, {c, left, right});
        for (int repeat = 0; repeat < 3; ++repeat) {
            solver.push();
            solver.assertFormula(op(Kind::Eq, {choice, op(Kind::Add, {base, constant(1)})}));
            CHECK(static_cast<int>(solver.checkSat()) == static_cast<int>(Result::Unsat));
            solver.pop();
            solver.push();
            solver.assertFormula(op(Kind::Eq, {choice, left}));
            CHECK(static_cast<int>(solver.checkSat()) == static_cast<int>(Result::Sat));
            solver.push();
            solver.assertFormula(op(Kind::Not, {c}));
            CHECK(static_cast<int>(solver.checkSat()) == static_cast<int>(Result::Unsat));
            solver.pop();
            CHECK(static_cast<int>(solver.checkSat()) == static_cast<int>(Result::Sat));
            solver.pop();
        }
    }
}
