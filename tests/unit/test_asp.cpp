#include "applications/satisfiability/asp/Solver.h"
#include <doctest/doctest.h>
#include <sstream>

using namespace xolver;
namespace asp = applications::satisfiability::asp;
namespace {
using Mask = unsigned;
bool literal(asp::Literal value, Mask mask) {
    const auto index = unsigned(value < 0 ? -value : value)-1;
    return bool(mask & (1u << index)) == (value > 0);
}
bool body(const asp::Rule& rule, Mask positive, Mask negative) {
    mpz_class sum = 0;
    for (const auto& term : rule.body) {
        const bool value = literal(term.literal, term.literal > 0 ? positive : negative);
        if (!rule.weighted && !value) return false;
        if (value) sum += term.weight;
    }
    return !rule.weighted || sum >= rule.lowerBound;
}
// Independent subset-minimality oracle for the candidate's reduct. It does not
// reproduce the production worklist closure or its unfounded-set computation.
bool reference(const asp::Program& program, Mask candidate) {
    auto modelsReduct = [&](Mask subset) {
        for (const auto& rule : program.rules) {
            if (!body(rule, subset, candidate)) continue;
            if (rule.choice) {
                for (const auto head : rule.head)
                    if ((candidate & (1u << (head-1))) && !(subset & (1u << (head-1)))) return false;
            } else {
                bool head = false;
                for (const auto atom : rule.head) head |= subset & (1u << (atom-1));
                if (!head) return false;
            }
        }
        return true;
    };
    if (!modelsReduct(candidate)) return false;
    for (Mask subset = candidate;; subset = (subset-1) & candidate) {
        if (subset != candidate && modelsReduct(subset)) return false;
        if (!subset) break;
    }
    for (const auto assumption : program.assumptions)
        if (!literal(assumption, candidate)) return false;
    return true;
}
asp::Rule normal(std::vector<asp::Atom> head, std::initializer_list<asp::Literal> body = {}, bool choice = false) {
    asp::Rule result;
    result.head = std::move(head);
    result.choice = choice;
    for (const auto lit : body) result.body.push_back({lit, 1});
    return result;
}
}

TEST_CASE("asp: normal, choice and weighted recursion match independent reduct minimality") {
    const std::vector<asp::Rule> pool{
        normal({1}, {2}), normal({2}, {1}), normal({1}, {-2}), normal({2}, {-1}),
        normal({1}, {1}, true), normal({1, 2}, {}, true), normal({}, {1, 2}),
        {false, {1}, true, 2, {{1, 1}, {2, 2}, {-3, 1}}},
        {false, {3}, true, 1, {{3, 1}, {-1, 1}}},
        {true, {2, 3}, true, 2, {{1, 2}, {-3, 1}}}};
    asp::Solver solver;
    CHECK(solver.category() == applications::Category::Satisfiability);
    for (unsigned k = 0; k < 80; ++k) {
        asp::Program program;
        program.rules = {pool[k % pool.size()], pool[(k*3+1) % pool.size()], pool[(k*7+4) % pool.size()]};
        for (Mask candidate = 0; candidate < 8; ++candidate) {
            auto constrained = program;
            for (int atom = 1; atom <= 3; ++atom)
                constrained.assumptions.push_back(candidate & (1u << (atom-1)) ? atom : -atom);
            const auto answer = solver.solve({constrained, {}});
            INFO(k, ": ", candidate, ": ", answer.reason);
            CHECK(answer.status == (reference(program, candidate) ? asp::Status::Sat : asp::Status::Unsat));
        }
    }
}

TEST_CASE("asp: positive cycles cannot support themselves") {
    asp::Problem problem;
    problem.program.rules = {normal({1}, {2}), normal({2}, {1}), normal({}, {-1})};
    const auto answer = asp::Solver().solve(problem);
    CHECK(answer.status == asp::Status::Unsat);
    CHECK(answer.unfoundedCuts > 0);
    problem.program.rules.pop_back();
    const auto empty = asp::Solver().solve(problem);
    REQUIRE(empty.status == asp::Status::Sat);
    REQUIRE(empty.model);
    CHECK(empty.model->empty());
}

TEST_CASE("asp: lexicographic signed objectives and output conditions remain exact") {
    asp::Problem problem;
    problem.program.rules = {normal({1, 2}, {}, true), normal({}, {1, 2})};
    const mpz_class large = mpz_class(1) << 100;
    problem.program.objectives = {{-2, {{1, -large}, {-2, 3}}}, {5, {{2, -1}, {2, -2}}}};
    problem.program.output = {{"one", {1}}, {"two", {2}}, {"two", {2}}, {"not-one", {-1}}};
    const auto answer = asp::Solver().solve(problem);
    INFO(answer.reason);
    REQUIRE(answer.status == asp::Status::Optimal);
    REQUIRE(answer.model);
    CHECK(*answer.model == std::vector<asp::Atom>{2});
    CHECK(answer.priorities == std::vector<std::int64_t>{5, -2});
    CHECK(answer.costs == std::vector<mpz_class>{-3, 0});
    CHECK(answer.shown == std::vector<std::string>{"two", "not-one"});
    CHECK(answer.provedLevels == 2);
}

TEST_CASE("asp: bounded or unsupported reasoning cannot claim an optimum") {
    asp::Problem problem;
    problem.program.rules = {normal({1}, {}, true)};
    problem.program.objectives = {{0, {{1, 1}}}};
    problem.limits.formulaWork = 1;
    CHECK(asp::Solver().solve(problem).status == asp::Status::Unknown);
    problem.limits = {};
    std::stop_source stop;
    stop.request_stop();
    problem.limits.stop = stop.get_token();
    CHECK(asp::Solver().solve(problem).status == asp::Status::Unknown);
    problem.limits = {};
    problem.program.rules = {normal({1, 2})};
    CHECK(asp::Solver().solve(problem).status == asp::Status::Unsupported);
    problem.program.rules = {normal({0})};
    CHECK(asp::Solver().solve(problem).status == asp::Status::InvalidInput);
}

TEST_CASE("aspif: parse exact strings and fail closed on unsupported directives") {
    std::istringstream valid("asp 1 0 0\n1 1 2 1 2 0 0\n2 -7 2 1 -3 -2 4\n4 5 hello 1 1\n6 1 -2\n0\n");
    const auto parsed = asp::parseAspif(valid);
    REQUIRE(parsed.status == asp::ParseResult::Status::Parsed);
    REQUIRE(parsed.program.rules.size() == 1);
    CHECK(parsed.program.rules.front().choice);
    CHECK(parsed.program.objectives.front().terms.front().weight == -3);
    CHECK(parsed.program.output.front().text == "hello");
    CHECK(parsed.program.assumptions == std::vector<asp::Literal>{-2});
    for (const char* input : {"asp 1 0 0\n1 0 2 1 2 0 0\n0\n", "asp 1 0 0\n5 1 2\n0\n", "asp 1 0 0 incremental\n0\n"}) {
        std::istringstream stream(input);
        CHECK(asp::parseAspif(stream).status == asp::ParseResult::Status::Unsupported);
    }
    for (const char* input : {"asp 1 0 0\n1 0 1 0 0 0\n0\n", "asp 1 0 0\n4 9 short\n0\n", "asp 1 0 0\n"}) {
        std::istringstream stream(input);
        CHECK(asp::parseAspif(stream).status == asp::ParseResult::Status::InvalidInput);
    }
}
