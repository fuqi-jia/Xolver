#include <doctest/doctest.h>
#include "applications/satisfiability/smt/Solver.h"
#include "applications/satisfiability/smt/TheoryFactory.h"
#include "search/coordination/TheoryLemmaDatabase.h"
#include "search/sat/CadicalBackend.h"
#include "search/sat/CadicalTheoryPropagator.h"
#include "applications/verification/pa/Presburger.h"
#include "applications/verification/sl/Solver.h"
#include "applications/optimization/omt/Optimize.h"
#include "quantifiers/FiniteFormula.h"
#include <somtparser/frontend/parser.h>
#include <type_traits>

using namespace xolver;

TEST_CASE("application dispatch: quantified inputs never reach ground callbacks") {
    int calls = 0;
    applications::satisfiability::smt::Solver solver([&](const applications::satisfiability::smt::Problem&) {
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
    applications::satisfiability::smt::Solver solver([&](const applications::satisfiability::smt::Problem&) {
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

TEST_CASE("application dispatch: factory connects theory model decisions for every arithmetic route") {
    struct Route {
        const char* logic;
        TheoryId owner;
        bool nonlinear;
    };
    for (const auto& route : std::vector<Route>{
        {"QF_LIA", TheoryId::LIA, false}, {"LIA", TheoryId::LIA, false},
        {"ALL", TheoryId::LIA, false}, {"", TheoryId::LIA, false},
        {"QF_LRA", TheoryId::LRA, false}, {"LRA", TheoryId::LRA, false},
        {"ALL", TheoryId::LRA, false}, {"QF_NIA", TheoryId::LIA, true},
        {"NIA", TheoryId::LIA, true}, {"QF_NRA", TheoryId::LRA, true},
        {"NRA", TheoryId::LRA, true}}) {
        CAPTURE(route.logic);
        NativeTerms terms;
        LogicFeatures features;
        features.hasInt = features.hasIntVar = route.owner == TheoryId::LIA;
        features.hasReal = features.hasRealVar = route.owner == TheoryId::LRA;
        features.hasNonlinear = route.nonlinear;
        CadicalBackend backend;
        TheoryAtomRegistry registry;
        TheoryManager manager;
        std::unique_ptr<SharedTermRegistry> shared;
        const auto result = setupSolvers(route.logic, features, &terms, registry, manager, shared, NullSort);
        REQUIRE(result.success);
        auto* arithmetic = manager.solverFor(route.owner);
        REQUIRE(arithmetic);
        TheoryLemmaDatabase lemmas;
        CadicalTheoryPropagator propagator{registry, manager, lemmas, backend};
        backend.connectPropagator(&propagator);
        struct Disconnect {
            CadicalBackend& backend;
            ~Disconnect() { backend.disconnectPropagator(); }
        } disconnect{backend};
        registry.setContext(&backend, nullptr);
        for (SatVar variable = 1; variable <= 4; ++variable)
            REQUIRE(backend.newVar() == variable);
        const mpq_class large(mpz_class("9007199254740992"));
        const LinearFormKey x{{{"factory-x", 1}}};
        registry.registerParsedTheoryAtom(1, NullExpr, route.owner,
            LinearAtomPayload{x, Relation::Eq, RealValue::fromMpq(large)});
        registry.registerParsedTheoryAtom(2, NullExpr, route.owner,
            LinearAtomPayload{x, Relation::Eq, RealValue::fromMpq(large + 1)});
        registry.registerParsedTheoryAtom(3, NullExpr, route.owner,
            LinearAtomPayload{x, Relation::Lt, RealValue::fromMpq(large + 1)});
        registry.registerParsedTheoryAtom(4, NullExpr, route.owner,
            LinearAtomPayload{LinearFormKey{{{"absent-coordinate", 1}}},
                              Relation::Leq, RealValue::fromInt(1)});
        propagator.notify_assignment({1});
        REQUIRE(arithmetic->check(lemmas, TheoryEffort::Full).kind == TheoryCheckResult::Kind::Consistent);
        const auto count = registry.numAtomVars();
        const auto unequal = manager.evalTheoryAtom(2);
        const auto strict = manager.evalTheoryAtom(3);
        REQUIRE(unequal.has_value());
        REQUIRE(strict.has_value());
        CHECK_FALSE(*unequal);
        CHECK(*strict);
        CHECK_FALSE(manager.evalTheoryAtom(4).has_value());
        CHECK(propagator.cb_decide() == -2);
        CHECK(propagator.cb_decide() == 3);
        CHECK(registry.numAtomVars() == count);
    }
}

TEST_CASE("application dispatch: independent applications share the typed abstract base") {
    static_assert(std::is_base_of_v<applications::Solver, applications::satisfiability::smt::Solver>);
    static_assert(std::is_base_of_v<applications::Solver, pa::Solver>);
    static_assert(std::is_base_of_v<applications::Solver, sl::Solver>);
    static_assert(std::is_base_of_v<applications::Solver, applications::optimization::omt::Solver>);
    pa::Solver integer;
    applications::TypedSolver<pa::Problem, pa::Decision>& typed = integer;
    SOMTParser::Parser parser;
    REQUIRE(parser.parseStr("(set-logic LIA)(assert (exists ((x Int)) (= (* 2 x) 1)))"));
    CHECK((typed.solve(parser.getAssertions()).result == Result::Unsat));
    CHECK((integer.family() == applications::Family::SoftwareVerification));
}
