#include <doctest/doctest.h>
#include <xolver/Solver.h>
#include "contracts/LogicFeatureDetector.h"
#include "frontend/preprocess/ToIntDefinitionalLowerer.h"
#include "frontend/preprocess/IntDivModLowerer.h"
#include <string>
#include <utility>
#include <vector>

using namespace xolver;

TEST_CASE("Arithmetic witnesses: generated floor domains participate in routing") {
    for (bool constant : {false, true}) {
        NativeTerms terms;
        terms.registerSort(0, SortKind::Int);
        terms.registerSort(1, SortKind::Real);
        terms.registerSort(2, SortKind::Bool);
        terms.setBoolSortId(2);
        const auto argument = constant
            ? terms.add({Kind::ConstReal, 1, {}, Payload(std::string("1/2"))})
            : terms.add({Kind::Variable, 1, {}, Payload(std::string("x"))});
        const auto floor = terms.add({Kind::ToInt, 0, {argument}, {}});
        const auto zero = terms.add({Kind::ConstInt, 0, {}, Payload(int64_t(0))});
        terms.addAssertion(terms.add({Kind::Eq, 2, {floor, zero}, {}}));
        ToIntDefinitionalLowerer lowerer(terms);
        REQUIRE(lowerer.run());
        lowerer.commit();
        CHECK(lowerer.hadIntBridge());
        CHECK(lowerer.hadRealBridge());
        const auto features = LogicFeatureDetector(terms).detect();
        CHECK(features.hasIntVar);
        CHECK(features.hasRealVar);
        CHECK(features.hasMixedIntReal);
    }
}

TEST_CASE("Arithmetic witnesses: generated quotient and remainder remain integer") {
    NativeTerms terms;
    terms.registerSort(0, SortKind::Int);
    terms.registerSort(1, SortKind::Real);
    terms.registerSort(2, SortKind::Bool);
    terms.setBoolSortId(2);
    const auto four = terms.add({Kind::ConstInt, 0, {}, Payload(int64_t(4))});
    const auto three = terms.add({Kind::ConstInt, 0, {}, Payload(int64_t(3))});
    const auto division = terms.add({Kind::Div, 0, {four, three}, {}});
    const auto cast = terms.add({Kind::ToReal, 1, {division}, {}});
    const auto y = terms.add({Kind::Variable, 1, {}, Payload(std::string("y"))});
    terms.addAssertion(terms.add({Kind::Eq, 2, {cast, y}, {}}));
    IntDivModLowerer lowerer(terms);
    REQUIRE(lowerer.run());
    lowerer.commit();
    const auto features = LogicFeatureDetector(terms).detect();
    CHECK(features.hasIntVar);
    CHECK(features.hasMixedIntReal);
}

TEST_CASE("Arithmetic witnesses: is_int Boolean equivalence retains exact semantics") {
    for (const auto& logic : {"ALL", "QF_LIRA"}) {
        for (const auto& [value, integral] : std::vector<std::pair<std::string, bool>>{
                {"1", true}, {"-2", true}, {"1/2", false}, {"-3/2", false}}) {
            for (bool wanted : {false, true}) {
                CAPTURE(logic);
                CAPTURE(value);
                CAPTURE(wanted);
                Solver solver;
                solver.setLogic(logic);
                const auto y = solver.mkConst(solver.realSort(), "y");
                const auto choice = solver.mkConst(solver.boolSort(), "choice");
                auto op = [&](Kind kind, std::vector<Term> children) {
                    return solver.mkOp(static_cast<uint32_t>(kind), std::move(children));
                };
                solver.assertFormula(op(Kind::Geq, {y, solver.mkReal(value)}));
                solver.assertFormula(op(Kind::Leq, {y, solver.mkReal(value)}));
                solver.assertFormula(op(Kind::Eq, {choice, op(Kind::IsInt, {y})}));
                solver.assertFormula(wanted ? choice : op(Kind::Not, {choice}));
                const auto expected = wanted == integral ? Result::Sat : Result::Unsat;
                REQUIRE((solver.checkSat() == expected));
                if (expected == Result::Sat)
                    CHECK(solver.validateModel() == Solver::ModelValidation::Satisfied);
            }
        }
    }
}

TEST_CASE("Arithmetic witnesses: nonlinear floor constraints select mixed arithmetic") {
    for (const auto& value : {"1", "1/2"}) for (bool wanted : {false, true}) {
        CAPTURE(value);
        CAPTURE(wanted);
        Solver solver;
        solver.setLogic("ALL");
        const auto y = solver.mkConst(solver.realSort(), "y");
        auto op = [&](Kind kind, std::vector<Term> children) {
            return solver.mkOp(static_cast<uint32_t>(kind), std::move(children));
        };
        solver.assertFormula(op(Kind::Geq, {y, solver.mkReal(value)}));
        solver.assertFormula(op(Kind::Leq, {y, solver.mkReal(value)}));
        const auto predicate = op(Kind::IsInt, {op(Kind::Mul, {y, y})});
        solver.assertFormula(wanted ? predicate : op(Kind::Not, {predicate}));
        const bool integral = std::string(value) == "1";
        REQUIRE((solver.checkSat() == (wanted == integral ? Result::Sat : Result::Unsat)));
        if (wanted == integral)
            CHECK(solver.validateModel() == Solver::ModelValidation::Satisfied);
    }
}

TEST_CASE("Arithmetic witnesses: NIRA checks polynomial and linear conjunctions together") {
    for (bool feasible : {false, true}) {
        Solver solver;
        solver.setLogic("QF_NIRA");
        const auto r = solver.mkConst(solver.realSort(), "r");
        const auto i = solver.mkConst(solver.intSort(), "i");
        auto op = [&](Kind kind, std::vector<Term> children) {
            return solver.mkOp(static_cast<uint32_t>(kind), std::move(children));
        };
        solver.assertFormula(op(Kind::Geq, {i, solver.mkInt(0)}));
        solver.assertFormula(op(Kind::Leq, {i, solver.mkInt(1)}));
        solver.assertFormula(op(Kind::Eq, {op(Kind::Mul, {r, r}), solver.mkReal("1")}));
        solver.assertFormula(op(Kind::Geq, {r, solver.mkReal(feasible ? "1" : "2")}));
        const auto expected = feasible ? Result::Sat : Result::Unsat;
        REQUIRE((solver.checkSat() == expected));
        if (feasible) CHECK(solver.validateModel() == Solver::ModelValidation::Satisfied);
    }
}

TEST_CASE("Arithmetic witnesses: Boolean integer dividend cannot yield a fractional quotient") {
    Solver solver;
    solver.setLogic("ALL");
    const auto p = solver.mkConst(solver.boolSort(), "p");
    const auto y = solver.mkConst(solver.realSort(), "y");
    auto op = [&](Kind kind, std::vector<Term> children) {
        return solver.mkOp(static_cast<uint32_t>(kind), std::move(children));
    };
    const auto dividend = op(Kind::Ite, {p, solver.mkInt(3), solver.mkInt(4)});
    const auto quotient = op(Kind::Div, {dividend, solver.mkInt(2)});
    solver.assertFormula(op(Kind::Eq, {y, op(Kind::ToReal, {quotient})}));
    solver.assertFormula(op(Kind::Geq, {y, solver.mkReal("3/2")}));
    solver.assertFormula(op(Kind::Leq, {y, solver.mkReal("3/2")}));
    CHECK((solver.checkSat() == Result::Unsat));
}
