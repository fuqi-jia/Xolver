#include "applications/smt/Solver.h"
#include "applications/sv/verification/Reachability.h"
#include "ir/NativeBuilder.h"
#include <doctest/doctest.h>
#include <queue>

using namespace xolver;
namespace v = applications::sv::verification;
namespace {
DecisionOracle oracle = [](const NativeAssertions &q) {
    return applications::smt::Solver().solve({q, {}, {}, {}});
};
} // namespace
TEST_CASE("SV reachability: synthesize an unbounded region without candidate templates") {
    native::Nodes b({});
    auto integers = SOMTParser::SortManager::getInt();
    auto booleans = SOMTParser::SortManager::getBool();
    auto x = b.make(integers, native::K::NT_VAR, {}, "x");
    auto xp = b.make(integers, native::K::NT_VAR, {}, "xp");
    auto mode = b.make(booleans, native::K::NT_VAR, {}, "mode");
    auto mp = b.make(booleans, native::K::NT_VAR, {}, "mp");
    auto zero = b.numeral(0);
    v::TransitionSystem s;
    s.state = {{x, xp}, {mode, mp}};
    s.initial = {b.equal(x, zero), mode};
    s.transition = {b.equal(mode, mp),
                    b.any({b.negate(mode), b.logical(native::K::NT_GE, {xp, zero})})};
    s.safety = b.logical(native::K::NT_GE, {x, zero});
    // Unreachable mode=false admits arbitrarily long spurious induction paths.
    CHECK(v::SafetySolver(oracle, {3}).solve({s, {}}).status == v::SafetyStatus::Unknown);
    auto answer = v::ReachabilitySolver(oracle, {3}).solve(s);
    INFO(answer.reason);
    REQUIRE(answer.status == v::SafetyStatus::Safe);
    REQUIRE(answer.certificate);
    CHECK(answer.certificate->depth == 1);
    CHECK(v::CertificateSolver(oracle).solve({s, *answer.certificate}).status == v::Status::Valid);
    s.safety = b.equal(x, zero);
    answer = v::ReachabilitySolver(oracle, {3}).solve(s);
    REQUIRE(answer.status == v::SafetyStatus::Unsafe);
    REQUIRE(answer.counterexample);
    CHECK(answer.counterexample->states.size() == 2);
    CHECK((oracle(answer.counterexample->query).result == Result::Sat));
}
TEST_CASE("SV reachability: fresh quantified inputs and immutable parameters") {
    native::Nodes b({});
    auto sort = b.bvSort(2);
    auto x = b.make(sort, native::K::NT_VAR, {}, "x");
    auto xp = b.make(sort, native::K::NT_VAR, {}, "xp");
    auto input = b.make(sort, native::K::NT_VAR, {}, "u");
    auto parameter = b.make(sort, native::K::NT_VAR, {}, "a");
    v::TransitionSystem s;
    s.state = {{x, xp}};
    s.parameters = {parameter};
    s.inputs = {input};
    s.initial = {b.equal(x, parameter)};
    s.transition = {b.equal(xp, input), b.equal(input, parameter)};
    s.safety = b.equal(x, parameter);
    auto answer = v::ReachabilitySolver(oracle, {2}).solve(s);
    REQUIRE(answer.status == v::SafetyStatus::Safe);
    CHECK(v::CertificateSolver(oracle).solve({s, *answer.certificate}).status == v::Status::Valid);
    s.initial = {b.equal(x, b.bv(0, 2))};
    s.parameters.clear();
    s.transition = {b.equal(xp, input)};
    s.safety = b.negate(b.equal(x, b.bv(2, 2)));
    answer = v::ReachabilitySolver(oracle, {2}).solve(s);
    REQUIRE(answer.status == v::SafetyStatus::Unsafe);
    CHECK(answer.counterexample->states.size() == 2);
}
TEST_CASE("SV reachability: symbolic fixed points agree with independent finite BFS") {
    unsigned random = 8191;
    auto draw = [&]() {
        random = random * 1664525u + 1013904223u;
        return random >> 16;
    };
    for (int sample = 0; sample < 24; ++sample) {
        INFO(sample);
        native::Nodes b({});
        auto sort = b.bvSort(2);
        auto x = b.make(sort, native::K::NT_VAR, {}, "x");
        auto xp = b.make(sort, native::K::NT_VAR, {}, "xp");
        NativeAssertions edges, starts, bad;
        bool graph[4][4]{};
        unsigned initial = 1u << (draw() % 4), violations = draw() & 15;
        int distance[4]{-1, -1, -1, -1};
        std::queue<int> pending;
        for (int i = 0; i < 4; ++i) {
            if (initial & (1u << i)) {
                starts.push_back(b.equal(x, b.bv(i, 2)));
                distance[i] = 0;
                pending.push(i);
            }
            if (violations & (1u << i))
                bad.push_back(b.equal(x, b.bv(i, 2)));
            for (int j = 0; j < 4; ++j)
                if ((graph[i][j] = draw() % 4 == 0))
                    edges.push_back(b.all({b.equal(x, b.bv(i, 2)), b.equal(xp, b.bv(j, 2))}));
        }
        int shortest = -1;
        while (!pending.empty()) {
            auto from = pending.front();
            pending.pop();
            if (violations & (1u << from)) {
                shortest = distance[from];
                break;
            }
            for (int to = 0; to < 4; ++to)
                if (graph[from][to] && distance[to] < 0) {
                    distance[to] = distance[from] + 1;
                    pending.push(to);
                }
        }
        v::TransitionSystem s{
            {{x, xp}}, {b.any(starts)}, {b.any(edges)}, {}, b.negate(b.any(bad)), {}, {}};
        auto answer = v::ReachabilitySolver(oracle, {4}).solve(s);
        INFO(answer.reason);
        REQUIRE(answer.status == (shortest < 0 ? v::SafetyStatus::Safe : v::SafetyStatus::Unsafe));
        if (shortest < 0)
            CHECK(v::CertificateSolver(oracle).solve({s, *answer.certificate}).status ==
                  v::Status::Valid);
        else
            CHECK(answer.counterexample->states.size() == std::size_t(shortest + 1));
    }
}
TEST_CASE("SV reachability: resource and oracle failures preserve unknown") {
    native::Nodes b({});
    auto x = b.make(SOMTParser::SortManager::getInt(), native::K::NT_VAR, {}, "x");
    auto xp = b.make(x->getSort(), native::K::NT_VAR, {}, "xp");
    v::TransitionSystem s{{{x, xp}},
                          {b.equal(x, b.numeral(0))},
                          {b.equal(xp, b.make(x->getSort(), native::K::NT_ADD, {x, b.numeral(1)}))},
                          {},
                          b.logical(native::K::NT_GE, {x, b.numeral(0)}),
                          {},
                          {}};
    CHECK(v::ReachabilitySolver(oracle, {0}).solve(s).status == v::SafetyStatus::Unknown);
    CHECK(v::ReachabilitySolver(oracle, {4, 1}).solve(s).status == v::SafetyStatus::Unknown);
    CHECK(v::ReachabilitySolver(oracle, {4, 2000000, 1}).solve(s).status ==
          v::SafetyStatus::Unknown);
    DecisionOracle unknown = [](const NativeAssertions &) { return SolverAnswer{}; };
    CHECK(v::ReachabilitySolver(unknown).solve(s).status == v::SafetyStatus::Unknown);
    s.safety = b.equal(xp, b.numeral(0));
    CHECK(v::ReachabilitySolver(oracle).solve(s).status == v::SafetyStatus::InvalidInput);
}
