#include "applications/maxsmt/Solver.h"
#include "applications/smt/Solver.h"
#include "ir/NativeBuilder.h"
#include "quantifiers/FiniteFormula.h"
#include <doctest/doctest.h>
#include <optional>

using namespace xolver;
namespace {
DecisionOracle maxsmtOracle = [](const NativeAssertions& roots) {
    return applications::smt::Solver().solve({roots, {}, {}, {}});
};
auto proposition(native::Nodes& nodes, const char* name) {
    return nodes.make(SOMTParser::SortManager::getBool(), native::K::NT_VAR, {}, name);
}
}

TEST_CASE("maxsmt: weighted soft formulas return an exact optimum and model") {
    using namespace applications::maxsmt;
    native::Nodes nodes({});
    auto a = proposition(nodes, "a"), b = proposition(nodes, "b");
    Problem problem;
    problem.hard = {nodes.negate(nodes.all({a, b}))};
    problem.soft = {{a, mpq_class(3, 2), "prefer-a"}, {b, 1, "prefer-b"}};
    Solver solver(maxsmtOracle);
    const auto answer = solver.solve(problem);
    INFO(answer.reason);
    REQUIRE(answer.status == Status::Optimal);
    REQUIRE(answer.cost);
    CHECK(*answer.cost == 1);
    CHECK(answer.lowerBound == 1);
    CHECK(answer.violatedSoft == std::vector<std::size_t>{1});
    REQUIRE(answer.model);
    CHECK(quantifiers::finiteValue(a, *answer.model) == "true");
    CHECK(quantifiers::finiteValue(b, *answer.model) == "false");
    CHECK(solver.family() == applications::Family::MaxSmt);
}

TEST_CASE("maxsmt: injected arithmetic backend preserves theory constraints") {
    using namespace applications::maxsmt;
    native::Nodes nodes({});
    auto x = nodes.make(SOMTParser::SortManager::getInt(), native::K::NT_VAR, {}, "x");
    auto low = nodes.logical(native::K::NT_LE, {x, nodes.numeral(0)});
    auto high = nodes.logical(native::K::NT_GE, {x, nodes.numeral(1)});
    Problem problem;
    problem.hard = {nodes.logical(native::K::NT_GE, {x, nodes.numeral(0)})};
    problem.soft = {{low, 2, "low"}, {high, 1, "high"}};
    const auto answer = Solver(maxsmtOracle).solve(problem);
    INFO(answer.reason);
    REQUIRE(answer.status == Status::Optimal);
    REQUIRE(answer.cost);
    CHECK(*answer.cost == 1);
    CHECK(answer.violatedSoft == std::vector<std::size_t>{1});
}

TEST_CASE("maxsmt: rational weighted results match independent truth-table enumeration") {
    using namespace applications::maxsmt;
    native::Nodes nodes({});
    auto a = proposition(nodes, "a"), b = proposition(nodes, "b"), c = proposition(nodes, "c");
    auto hard = nodes.all({nodes.negate(nodes.equal(a, c)), nodes.any({b, c})});
    for (int i = 0; i < 9; ++i) {
        std::vector<mpq_class> weights{mpq_class(i, 3), mpq_class(9-i, 2), mpq_class(i+1, 5)};
        std::optional<mpq_class> expected;
        for (int bits = 0; bits < 8; ++bits) {
            const bool av = bits & 1, bv = bits & 2, cv = bits & 4;
            if (av == cv || !(bv || cv)) continue;
            mpq_class cost = 0;
            if (!av) cost += weights[0];
            if (!bv) cost += weights[1];
            if (!cv) cost += weights[2];
            if (!expected || cost < *expected) expected = cost;
        }
        Problem problem;
        problem.hard = {hard};
        problem.soft = {{a, weights[0], {}}, {b, weights[1], {}}, {c, weights[2], {}}};
        auto answer = Solver(maxsmtOracle).solve(problem);
        INFO(i);
        INFO(answer.reason);
        REQUIRE(answer.status == Status::Optimal);
        REQUIRE(answer.cost);
        REQUIRE(expected);
        CHECK(*answer.cost == *expected);
    }
}

TEST_CASE("maxsmt: hard infeasibility, empty objectives and invalid inputs stay distinct") {
    using namespace applications::maxsmt;
    native::Nodes nodes({});
    Solver solver(maxsmtOracle);
    CHECK(solver.solve({{nodes.boolean(false)}, {}, {}}).status == Status::Infeasible);
    auto empty = solver.solve({{}, {}, {}});
    REQUIRE(empty.status == Status::Optimal);
    REQUIRE(empty.cost);
    CHECK(*empty.cost == 0);
    CHECK(solver.solve({{}, {{nodes.boolean(true), -1, {}}}, {}}).status == Status::InvalidInput);
    CHECK(solver.solve({{}, {{{}, 1, {}}}, {}}).status == Status::InvalidInput);
    CHECK(solver.solve({{nodes.numeral(1)}, {}, {}}).status == Status::InvalidInput);
    CHECK(Solver(DecisionOracle{}).solve({}).status == Status::Unknown);
}

TEST_CASE("maxsmt: cheaper unknown prevents an optimality claim") {
    using namespace applications::maxsmt;
    native::Nodes nodes({});
    auto p = proposition(nodes, "p");
    int calls = 0;
    Solver solver([&](const NativeAssertions&) {
        SolverAnswer answer;
        answer.result = ++calls == 2 ? Result::Unknown : Result::Sat;
        return answer;
    });
    auto answer = solver.solve({{}, {{p, 1, {}}}, {}});
    REQUIRE(answer.status == Status::Unknown);
    REQUIRE(answer.cost);
    CHECK(*answer.cost == 1);
    CHECK(answer.lowerBound == 0);
    calls = 0;
    auto zero = solver.solve({{}, {{p, 0, {}}}, {}});
    REQUIRE(zero.status == Status::Optimal);
    REQUIRE(zero.cost);
    CHECK(*zero.cost == 0);
}

TEST_CASE("maxsmt: resource exhaustion and cancellation cannot imply optimality") {
    using namespace applications::maxsmt;
    native::Nodes nodes({});
    auto p = proposition(nodes, "p");
    Solver solver(maxsmtOracle);
    Problem problem{{}, {{p, 1, {}}}, {}};
    problem.limits.oracleCalls = 1;
    const auto limited = solver.solve(problem);
    CHECK(limited.status == Status::Unknown);
    CHECK(limited.oracleCalls == 1);
    CHECK_FALSE(limited.cost);
    std::stop_source stop;
    stop.request_stop();
    problem.limits.stop = stop.get_token();
    const auto cancelled = solver.solve(problem);
    CHECK(cancelled.status == Status::Unknown);
    CHECK(cancelled.oracleCalls == 0);
    int calls = 0;
    Solver stateLimited([&](const NativeAssertions&) {
        SolverAnswer result;
        result.result = ++calls == 1 ? Result::Sat : Result::Unsat;
        return result;
    });
    problem.limits = {};
    problem.limits.states = 1;
    CHECK(stateLimited.solve(problem).status == Status::Unknown);
}
