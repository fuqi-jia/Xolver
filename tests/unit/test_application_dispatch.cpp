#include <doctest/doctest.h>
#include "applications/smt/Solver.h"
#include "applications/smt/TheoryFactory.h"
#include "applications/sv/pa/Presburger.h"
#include "applications/sv/sl/Solver.h"
#include "applications/omt/Optimize.h"
#include "quantifiers/FiniteFormula.h"
#include <somtparser/frontend/parser.h>
#include <type_traits>

using namespace xolver;

TEST_CASE("application dispatch: quantified inputs never reach ground callbacks") {
    int calls = 0;
    applications::smt::Solver solver([&](const applications::smt::Problem&) {
        ++calls;
        SolverAnswer answer;
        answer.result = Result::Sat;
        return answer;
    });
    for (const auto& [body, expected] : std::vector<std::pair<std::string, Result>>{
        {"(forall ((x Int)) (exists ((y Int)) (= y (+ x 1))))", Result::Sat},
        {"(exists ((x Int)) (= (* 2 x) 1))", Result::Unsat},
        {"(forall ((x Real)) (>= (* x x) 0))", Result::Sat},
        {"(forall ((x Int)) (f x))", Result::Unknown}}) {
        SOMTParser::Parser parser;
        REQUIRE(parser.parseStr("(set-logic ALL)(declare-fun f (Int) Bool)(assert " + body + ")"));
        auto result = solver.solve({parser.getAssertions(), {}, {}});
        INFO(body);
        CHECK((result.result == expected));
        CHECK((calls == 0));
        if (expected == Result::Unknown) CHECK((result.reason.find("first-order") != std::string::npos));
    }
}

TEST_CASE("application dispatch: memory encoded as arrays stays SMT") {
    SOMTParser::Parser parser;
    REQUIRE(parser.parseStr("(set-logic ALL)(declare-const heap (Array Int Int))"
                            "(declare-const pointer Int)(assert (= (select heap pointer) 3))"));
    int calls = 0;
    applications::smt::Solver solver([&](const applications::smt::Problem&) {
        ++calls;
        SolverAnswer answer;
        answer.result = Result::Sat;
        return answer;
    });
    CHECK((solver.solve({parser.getAssertions(), {}, {}}).result == Result::Sat));
    CHECK((calls == 1));
    SOMTParser::Parser spatial;
    REQUIRE(spatial.parseStr("(set-logic ALL)(declare-heap (Int Int))(assert sep.emp)"));
    auto rejected = solver.solve({spatial.getAssertions(), {}, {}});
    CHECK((rejected.result == Result::Unknown));
    CHECK((calls == 1));
    sl::Solver separation;
    sl::Request request;
    request.location = spatial.getHeapLocationSort();
    request.data = spatial.getHeapDataSort();
    request.assertions = spatial.getAssertions();
    CHECK((separation.solve(request).result == Result::Sat));
}

TEST_CASE("application dispatch: QF factory rejects binders before constructing a stack") {
    LogicFeatures features;
    features.hasQuantifier = true;
    TheoryAtomRegistry registry;
    TheoryManager manager;
    std::unique_ptr<SharedTermRegistry> shared;
    auto result = setupSolvers("NRA", features, nullptr, registry, manager, shared, NullSort);
    CHECK_FALSE(result.success);
    CHECK((result.polyKernelRaw == nullptr));
}

TEST_CASE("application dispatch: independent applications share the typed abstract base") {
    static_assert(std::is_base_of_v<applications::Solver, applications::smt::Solver>);
    static_assert(std::is_base_of_v<applications::Solver, pa::Solver>);
    static_assert(std::is_base_of_v<applications::Solver, sl::Solver>);
    static_assert(std::is_base_of_v<applications::Solver, applications::omt::Solver>);
    pa::Solver integer;
    applications::TypedSolver<pa::Problem, pa::Decision>& typed = integer;
    SOMTParser::Parser parser;
    REQUIRE(parser.parseStr("(set-logic LIA)(assert (exists ((x Int)) (= (* 2 x) 1)))"));
    CHECK((typed.solve(parser.getAssertions()).result == Result::Unsat));
    CHECK((integer.family() == applications::Family::SoftwareVerification));
}
