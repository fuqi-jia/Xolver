#include "xolver/Solver.h"
#include "applications/verification/model_checking/Solver.h"
#include "frontend/parser/NativeTheoryPolicy.h"
#include "ir/NativeBuilder.h"
#include <doctest/doctest.h>
#include <somtparser/frontend/parser.h>

using namespace xolver;
namespace context_v = applications::verification::model_checking;
namespace {
DecisionOracle contextDecision = [](const NativeAssertions &query) {
    return Solver().decide(query);
};
context_v::Obligation obligation(const std::string &source) {
    SOMTParser::Parser parser;
    preserveNativeTheories(*parser.getOptions());
    if (!parser.parseStr(source))
        throw std::runtime_error("invalid context test input");
    auto assertions = parser.getAssertions();
    if (assertions.empty())
        throw std::runtime_error("missing context test conclusion");
    auto conclusion = assertions.back();
    assertions.pop_back();
    return {"context", assertions, conclusion};
}
} // namespace

TEST_CASE("SV context: infeasibility and implication are distinct across theories") {
    for (const auto &source : {
             "(declare-const x Int) (assert (< x x)) (assert true)",
             "(declare-const x Real) (assert (< x x)) (assert true)",
             "(declare-const x (_ BitVec 8)) (assert (bvult x x)) (assert true)",
             "(declare-const a (Array Int Int)) (assert (distinct (select a 0) (select a 0))) (assert true)",
             "(declare-sort U 0) (declare-const x U) (assert (distinct x x)) (assert true)"}) {
        INFO(std::string(source));
        auto task = obligation(std::string("(set-logic ALL) ") + source);
        auto answer = context_v::ContextSolver(contextDecision).solve(task);
        INFO(answer.implication.reason);
        CHECK((answer.context.result == Result::Unsat));
        CHECK(answer.implication.status == context_v::Status::Valid);
        CHECK(answer.queries == 1);
        CHECK_FALSE(answer.implication.counterexample);
        // Ordinary implication checking correctly remains vacuously valid.
        CHECK(context_v::Solver(contextDecision).solve({{task}}).status == context_v::Status::Valid);
    }
}

TEST_CASE("SV context: feasible goals retain models and do not mutate assumptions") {
    for (const auto &source : {
             "(declare-const x Int) (assert (= x 2)) (assert (= x 2))",
             "(declare-const x Real) (assert (= x (/ 1 2))) (assert (> x 0))",
             "(declare-const x (_ BitVec 8)) (assert (= x #x02)) (assert (= x #x02))",
             "(declare-const a (Array Int Int)) (assert (= (select a 0) 2)) (assert (= (select a 0) 2))"}) {
        INFO(std::string(source));
        auto task = obligation(std::string("(set-logic ALL) ") + source);
        const auto original = task.assumptions;
        auto answer = context_v::ContextSolver(contextDecision).solve(task);
        CHECK((answer.context.result == Result::Sat));
        CHECK(answer.implication.status == context_v::Status::Valid);
        CHECK(answer.queries == 2);
        CHECK(task.assumptions == original);
        native::Nodes b({});
        task.conclusion = b.boolean(false);
        answer = context_v::ContextSolver(contextDecision).solve(task);
        REQUIRE((answer.context.result == Result::Sat));
        REQUIRE(answer.implication.status == context_v::Status::Invalid);
        CHECK(answer.implication.counterexample.has_value());
        CHECK(answer.queries == 2);
        CHECK(task.assumptions == original);
    }
}

TEST_CASE("SV context: an undecided context never becomes an infeasible path") {
    native::Nodes b({});
    context_v::Obligation task{"unknown", {b.boolean(true)}, b.boolean(true)};
    for (auto result : {Result::Sat, Result::Unsat, Result::Unknown}) {
        unsigned calls = 0;
        DecisionOracle oracle = [&](const NativeAssertions &snapshot) {
            ++calls;
            SolverAnswer answer;
            if (calls == 1) {
                CHECK(snapshot == task.assumptions);
                answer.reason = "context budget exhausted";
            } else {
                REQUIRE(snapshot.size() == 2);
                CHECK(snapshot.front() == task.assumptions.front());
                CHECK(snapshot.back()->getKind() == native::K::NT_NOT);
                answer.result = result;
                answer.reason = "implication budget exhausted";
                if (result == Result::Sat)
                    answer.model = TheoryModel{};
            }
            return answer;
        };
        auto answer = context_v::ContextSolver(oracle).solve(task);
        CHECK((answer.context.result == Result::Unknown));
        CHECK(answer.context.reason == "context budget exhausted");
        CHECK(answer.queries == 2);
        CHECK(calls == 2);
        CHECK(answer.implication.status == (result == Result::Sat ? context_v::Status::Invalid
                                           : result == Result::Unsat ? context_v::Status::Valid
                                                                     : context_v::Status::Unknown));
        if (result == Result::Unknown)
            CHECK(answer.implication.reason == "implication budget exhausted");
        CHECK(bool(answer.implication.counterexample) == (result == Result::Sat));
    }
}

TEST_CASE("SV context: invalid inputs and oracle failures preserve uncertainty") {
    native::Nodes b({});
    context_v::Obligation task{"bad", {}, b.boolean(true)};
    unsigned calls = 0;
    DecisionOracle oracle = [&](const NativeAssertions &) {
        ++calls;
        throw std::runtime_error("oracle cancelled");
        return SolverAnswer{};
    };
    context_v::ContextSolver solver(oracle);
    for (auto bad : {native::Node{}, b.numeral(3)}) {
        task.assumptions = {bad};
        auto answer = solver.solve(task);
        CHECK(answer.implication.status == context_v::Status::InvalidInput);
        CHECK((answer.context.result == Result::Unknown));
        CHECK(answer.queries == 0);
        task.assumptions.clear();
        task.conclusion = bad;
        CHECK(solver.solve(task).implication.status == context_v::Status::InvalidInput);
        task.conclusion = b.boolean(true);
    }
    CHECK(calls == 0);
    auto answer = solver.solve(task);
    CHECK((answer.context.result == Result::Unknown));
    CHECK(answer.implication.status == context_v::Status::Unknown);
    CHECK(answer.implication.reason == "oracle cancelled");
    CHECK(answer.queries == 1);
    CHECK(calls == 1);
    answer = context_v::ContextSolver({}).solve(task);
    CHECK(answer.queries == 0);
    CHECK(answer.implication.status == context_v::Status::Unknown);
    CHECK(answer.implication.reason == "decision oracle is not attached");
}

TEST_CASE("SV context: a failed implication keeps the completed feasibility verdict") {
    native::Nodes b({});
    unsigned calls = 0;
    context_v::ContextSolver solver([&](const NativeAssertions &) {
        if (++calls == 2)
            throw std::runtime_error("refutation cancelled");
        SolverAnswer answer;
        answer.result = Result::Sat;
        answer.model = TheoryModel{};
        return answer;
    });
    auto answer = solver.solve({"failure", {}, b.boolean(true)});
    CHECK((answer.context.result == Result::Sat));
    CHECK(answer.context.model.has_value());
    CHECK(answer.implication.status == context_v::Status::Unknown);
    CHECK(answer.implication.reason == "refutation cancelled");
    CHECK(answer.queries == 2);
}

TEST_CASE("API: native snapshots are transactional and isolate previous scopes") {
    native::Nodes b({});
    Solver solver;
    solver.setOption("seed", OptionValue(int64_t(13)));
    auto old = solver.mkBool(true);
    solver.assertFormula(old);
    solver.push();
    solver.assertFormula(solver.mkBool(false));
    CHECK_THROWS_AS(solver.decide({b.numeral(1)}), std::invalid_argument);
    CHECK_THROWS_AS(solver.decide({{}}), std::invalid_argument);
    auto first = b.make(SOMTParser::SortManager::getInt(), native::K::NT_VAR, {}, "alias");
    auto second = b.make(SOMTParser::SortManager::getInt(), native::K::NT_VAR, {}, "alias");
    CHECK_THROWS_AS(solver.decide({b.equal(first, b.numeral(1)),
                                  b.equal(second, b.numeral(2))}), std::invalid_argument);
    CHECK((solver.checkSat() == Result::Unsat));
    solver.pop();
    CHECK((solver.checkSat() == Result::Sat));
    auto task = obligation("(set-logic ALL)(declare-const x Real)"
                           "(assert (= x (/ 1 2)))(assert true)");
    auto original = task.assumptions.front();
    auto answer = solver.decide(task.assumptions);
    REQUIRE((answer.result == Result::Sat));
    REQUIRE(answer.model);
    CHECK(answer.model->numericAssignments.at("x") == RealValue::fromMpq(mpq_class(1, 2)));
    CHECK((solver.validateModel() == Solver::ModelValidation::Satisfied));
    CHECK(solver.getOption("seed").i == 13);
    CHECK_THROWS_AS(solver.assertFormula(old), std::invalid_argument);
    CHECK(task.assumptions.front() == original);
    solver.push();
    solver.assertFormula(solver.mkBool(false));
    CHECK((solver.checkSat() == Result::Unsat));
    solver.pop();
    CHECK((solver.checkSat() == Result::Sat));
    CHECK((solver.decide({b.boolean(false)}).result == Result::Unsat));
    CHECK((solver.decide({}).result == Result::Sat));
    CHECK((solver.decide(task.assumptions).result == Result::Sat));
}
