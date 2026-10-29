#include "applications/satisfiability/sat/Solver.h"
#include "applications/satisfiability/smt/Solver.h"
#include "applications/optimization/maxsat/Solver.h"
#include <doctest/doctest.h>
#include <limits>

using namespace xolver;
namespace {
bool clauseHolds(const std::vector<int>& clause, unsigned bits) {
    for (int value : clause)
        if (bool(bits & (1u << (std::abs(value)-1))) == (value > 0)) return true;
    return false;
}
}

TEST_CASE("sat application: models and assumptions agree with independent enumeration") {
    using namespace applications::satisfiability::sat;
    Solver solver;
    CHECK(solver.category() == applications::Category::Satisfiability);
    const std::vector<Clause> clauses{{1}, {-1}, {2}, {-2}, {1, 2}, {-1, 2}, {1, -2}, {-1, -2}, {}};
    for (unsigned mask = 0; mask < 64; ++mask) {
        Problem problem;
        problem.variables = 2;
        for (unsigned i = 0; i < 6; ++i)
            if (mask & (1u << i)) problem.clauses.push_back(clauses[i]);
        if (mask % 3 == 0) problem.assumptions = {-2};
        bool expected = false;
        for (unsigned bits = 0; bits < 4; ++bits) {
            bool valid = true;
            for (const auto& clause : problem.clauses) valid &= clauseHolds(clause, bits);
            for (int assumption : problem.assumptions) valid &= clauseHolds({assumption}, bits);
            expected |= valid;
        }
        const auto answer = solver.solve(problem);
        INFO(mask, ": ", answer.reason);
        CHECK(answer.status == (expected ? Status::Sat : Status::Unsat));
        if (expected) {
            unsigned bits = 0;
            for (const auto& [index, value] : answer.assignment)
                if (value) bits |= 1u << (index-1);
            for (const auto& clause : problem.clauses) CHECK(clauseHolds(clause, bits));
            for (int assumption : problem.assumptions) CHECK(clauseHolds({assumption}, bits));
        }
    }
    Problem emptyClause;
    emptyClause.clauses = {{}};
    CHECK(solver.solve(emptyClause).status == Status::Unsat);
    Problem sparse;
    sparse.variables = std::numeric_limits<int>::max();
    sparse.clauses = {{std::numeric_limits<int>::max()}};
    const auto answer = solver.solve(sparse);
    REQUIRE(answer.status == Status::Sat);
    CHECK(answer.assignment.size() == 1);
}

TEST_CASE("sat application: invalid indices and unavailable backends are explicit") {
    using namespace applications::satisfiability::sat;
    for (int value : {0, std::numeric_limits<int>::min(), 3}) {
        Problem problem;
        problem.variables = 2;
        problem.clauses = {{value}};
        CHECK(Solver().solve(problem).status == Status::InvalidInput);
    }
    CHECK(Solver(Solver::Factory{}).solve({}).status == Status::Unknown);
    Problem expired;
    expired.deadline = std::chrono::steady_clock::now() - std::chrono::seconds(1);
    expired.clauses = {{1, 2}, {-1, -2}};
    CHECK(Solver().solve(expired).status == Status::Unknown);
}

TEST_CASE("maxsat application: exact weighted clauses match independent enumeration") {
    using namespace applications::optimization::maxsat;
    Solver solver([](const NativeAssertions& roots) {
        return applications::satisfiability::smt::Solver().solve({roots, {}, {}, {}});
    });
    CHECK(solver.category() == applications::Category::Optimization);
    for (int k = 0; k < 8; ++k) {
        Problem problem;
        problem.hard = {{1, 2}, {-1, -2}};
        problem.soft = {{{1}, mpq_class(k+1, 3), "a"}, {{2}, mpq_class(9-k, 2), "b"},
                        {{}, mpq_class(1, 5), "always-violated"}};
        std::optional<mpq_class> expected;
        for (unsigned bits = 0; bits < 4; ++bits) {
            bool feasible = true;
            for (const auto& clause : problem.hard) feasible &= clauseHolds(clause, bits);
            if (!feasible) continue;
            mpq_class cost = 0;
            for (const auto& soft : problem.soft)
                if (!clauseHolds(soft.literals, bits)) {
                    auto weight = soft.weight;
                    weight.canonicalize();
                    cost += weight;
                }
            if (!expected || cost < *expected) expected = cost;
        }
        const auto answer = solver.solve(problem);
        INFO(k, ": ", answer.reason);
        REQUIRE(answer.status == Status::Optimal);
        REQUIRE(answer.cost);
        CHECK(*answer.cost == *expected);
    }
    Problem infeasible;
    infeasible.hard = {{}};
    CHECK(solver.solve(infeasible).status == Status::Infeasible);
    Problem invalid;
    invalid.soft = {{{0}, 1, {}}};
    CHECK(solver.solve(invalid).status == Status::InvalidInput);
    Problem cancelled;
    std::stop_source stop;
    stop.request_stop();
    cancelled.limits.stop = stop.get_token();
    CHECK(solver.solve(cancelled).status == Status::Unknown);
}
