#include "applications/satisfiability/smt/Solver.h"
#include "applications/verification/model_checking/ModelChecking.h"
#include "ir/NativeBuilder.h"
#include <doctest/doctest.h>
#include <queue>

using namespace xolver;
namespace v = applications::verification::model_checking;
namespace {
DecisionOracle decide = [](const NativeAssertions &q) {
    return applications::satisfiability::smt::Solver().solve({q, {}, {}, {}});
};
struct ArithmeticSystem {
    native::Nodes b{{}};
    native::Sort integers = SOMTParser::SortManager::getInt();
    native::Node x = variable("x"), xp = variable("xp");
    native::Node variable(const char *name) {
        return b.make(integers, native::K::NT_VAR, {}, name);
    }
    native::Node number(int n) {
        return b.make(integers, native::K::NT_CONST, {}, std::to_string(n));
    }
    native::Node add(native::Node a, int n) {
        return b.make(integers, native::K::NT_ADD, {a, number(n)});
    }
    native::Node nonnegative(native::Node a) { return b.logical(native::K::NT_GE, {a, number(0)}); }
    v::TransitionSystem system() {
        return {{{x, xp}}, {b.equal(x, number(0))}, {b.equal(xp, add(x, 1))},
                {},        nonnegative(x),          {},
                {}};
    }
};
} // namespace
TEST_CASE("SV safety: unbounded integer induction and checked certificates") {
    ArithmeticSystem a;
    auto system = a.system();
    auto answer = v::SafetySolver(decide, {4}).solve({system, {}});
    INFO(answer.reason);
    REQUIRE(answer.status == v::SafetyStatus::Safe);
    REQUIRE(answer.certificate);
    CHECK(answer.certificate->kind == v::SafetyProof::KInduction);
    CHECK(answer.certificate->depth == 1);
    CHECK(answer.queries > 0);
    CHECK(v::CertificateSolver(decide).solve({system, *answer.certificate}).status ==
          v::Status::Valid);
    auto forged = *answer.certificate;
    forged.invariant = {a.b.boolean(false)};
    CHECK(v::CertificateSolver(decide).solve({system, forged}).status == v::Status::Invalid);
    system.safety = a.b.logical(native::K::NT_LT, {a.x, a.number(0)});
    CHECK(v::CertificateSolver(decide).solve({system, *answer.certificate}).status ==
          v::Status::Invalid);
}
TEST_CASE("SV safety: reachable traces and bounded absence remain distinct") {
    ArithmeticSystem a;
    auto system = a.system();
    system.safety = a.b.logical(native::K::NT_LT, {a.x, a.number(3)});
    auto bounded = v::SafetySolver(decide, {2}, v::SafetyMethod::Bounded).solve({system, {}});
    CHECK(bounded.status == v::SafetyStatus::Unknown);
    CHECK(bounded.checkedDepth == std::optional<std::size_t>(2));
    CHECK_FALSE(bounded.certificate);
    auto answer = v::SafetySolver(decide, {4}).solve({system, {}});
    REQUIRE(answer.status == v::SafetyStatus::Unsafe);
    REQUIRE(answer.counterexample);
    REQUIRE(answer.counterexample->states.size() == 4);
    CHECK((decide(answer.counterexample->query).result == Result::Sat));
    REQUIRE(answer.counterexample->model);
    for (std::size_t i = 0; i < 4; ++i) {
        auto name = answer.counterexample->states[i][0]->getName();
        CHECK((answer.counterexample->model->numericAssignments.at(name) == RealValue::fromInt(i)));
    }
    system.initial = {a.b.boolean(false)};
    answer = v::SafetySolver(decide, {0}).solve({system, {}});
    REQUIRE(answer.status == v::SafetyStatus::Safe);
    CHECK(answer.certificate->kind == v::SafetyProof::ReachabilityDiameter);
}
TEST_CASE("SV safety: per-transition inputs are fresh and parameters are immutable") {
    ArithmeticSystem a;
    auto &b = a.b;
    auto system = a.system();
    auto input = b.make(SOMTParser::SortManager::getBool(), native::K::NT_VAR, {}, "input");
    system.inputs = {input};
    system.transition = {
        b.any({b.all({b.equal(a.x, a.number(0)), b.negate(input), b.equal(a.xp, a.number(1))}),
               b.all({b.equal(a.x, a.number(1)), input, b.equal(a.xp, a.number(2))})})};
    system.safety = b.logical(native::K::NT_LT, {a.x, a.number(2)});
    auto answer = v::SafetySolver(decide, {2}).solve({system, {}});
    INFO(answer.reason);
    REQUIRE(answer.status == v::SafetyStatus::Unsafe);
    REQUIRE(answer.counterexample);
    REQUIRE(answer.counterexample->inputs.size() == 2);
    REQUIRE(answer.counterexample->model);
    CHECK(answer.counterexample->model->assignments.at(
              answer.counterexample->inputs[0][0]->getName()) == "false");
    CHECK(answer.counterexample->model->assignments.at(
              answer.counterexample->inputs[1][0]->getName()) == "true");
    system = a.system();
    auto parameter = a.variable("parameter");
    system.parameters = {parameter};
    system.initial = {b.equal(a.x, parameter)};
    system.safety = b.logical(native::K::NT_GE, {a.x, parameter});
    CHECK(v::SafetySolver(decide, {2}).solve({system, {}}).status == v::SafetyStatus::Safe);
}
TEST_CASE("SV inference: removal rechecks dependent candidates and retains joint invariants") {
    ArithmeticSystem a;
    auto &b = a.b;
    auto system = a.system();
    auto y = a.variable("y"), yp = a.variable("yp");
    system.state.push_back({y, yp});
    system.initial.push_back(b.equal(y, a.number(0)));
    system.transition = {b.equal(a.xp, y), b.equal(yp, a.add(y, 1))};
    NativeAssertions candidates{b.equal(a.x, a.number(0)), b.equal(y, a.number(0)),
                                a.nonnegative(a.x), a.nonnegative(y)};
    auto inferred = v::InferenceSolver(decide).solve({system, candidates});
    INFO(inferred.reason);
    REQUIRE(inferred.status == v::InferenceStatus::Inductive);
    CHECK((inferred.retained == std::vector<std::size_t>{2, 3}));
    CHECK(inferred.refuted.size() == 2);
    CHECK(v::Solver(decide).solve({inferred.obligations}).status == v::Status::Valid);
    auto answer = v::SafetySolver(decide).solve({system, candidates});
    REQUIRE(answer.status == v::SafetyStatus::Safe);
    CHECK(answer.certificate->kind == v::SafetyProof::Invariant);
    CHECK(v::CertificateSolver(decide).solve({system, *answer.certificate}).status ==
          v::Status::Valid);
}
TEST_CASE("SV safety: k-induction advances beyond a spurious one-step predecessor") {
    ArithmeticSystem a;
    auto system = a.system();
    NativeAssertions edges;
    for (auto [from, to] :
         std::vector<std::pair<int, int>>{{0, 1}, {1, 2}, {2, 3}, {3, 3}, {4, 5}, {5, 5}})
        edges.push_back(a.b.all({a.b.equal(a.x, a.number(from)), a.b.equal(a.xp, a.number(to))}));
    system.transition = {a.b.any(edges)};
    system.safety = a.b.negate(a.b.equal(a.x, a.number(5)));
    auto answer = v::SafetySolver(decide, {3}).solve({system, {}});
    INFO(answer.reason);
    REQUIRE(answer.status == v::SafetyStatus::Safe);
    CHECK(answer.certificate->kind == v::SafetyProof::KInduction);
    CHECK(answer.certificate->depth == 2);
    CHECK(v::CertificateSolver(decide).solve({system, *answer.certificate}).status ==
          v::Status::Valid);
    auto broken = *answer.certificate;
    broken.depth = 1;
    CHECK(v::CertificateSolver(decide).solve({system, broken}).status == v::Status::Invalid);
}
TEST_CASE("SV safety: finite-state answers agree with independent explicit reachability") {
    unsigned state = 431;
    auto random = [&]() {
        state = state * 1664525u + 1013904223u;
        return state >> 16;
    };
    for (int sample = 0; sample < 32; ++sample) {
        INFO(sample);
        native::Nodes b({});
        auto sort = b.bvSort(2);
        auto x = b.make(sort, native::K::NT_VAR, {}, "x"),
             xp = b.make(sort, native::K::NT_VAR, {}, "xp");
        bool edges[4][4]{};
        NativeAssertions transitions, initial, bad;
        unsigned starts = random() & 15, violations = random() & 15;
        for (int i = 0; i < 4; ++i) {
            if (starts & (1u << i))
                initial.push_back(b.equal(x, b.bv(i, 2)));
            if (violations & (1u << i))
                bad.push_back(b.equal(x, b.bv(i, 2)));
            for (int j = 0; j < 4; ++j)
                if ((edges[i][j] = (random() % 3 == 0)))
                    transitions.push_back(b.all({b.equal(x, b.bv(i, 2)), b.equal(xp, b.bv(j, 2))}));
        }
        std::queue<int> pending;
        int distance[4]{-1, -1, -1, -1};
        for (int i = 0; i < 4; ++i)
            if (starts & (1u << i)) {
                pending.push(i);
                distance[i] = 0;
            }
        int shortest = -1;
        while (!pending.empty()) {
            int i = pending.front();
            pending.pop();
            if (violations & (1u << i)) {
                shortest = distance[i];
                break;
            }
            for (int j = 0; j < 4; ++j)
                if (edges[i][j] && distance[j] < 0) {
                    distance[j] = distance[i] + 1;
                    pending.push(j);
                }
        }
        v::TransitionSystem system{
            {{x, xp}}, {b.any(initial)}, {b.any(transitions)}, {}, b.negate(b.any(bad)), {}, {}};
        auto answer = v::SafetySolver(decide, {4}, v::SafetyMethod::Bounded).solve({system, {}});
        INFO(answer.reason);
        REQUIRE(answer.status == (shortest < 0 ? v::SafetyStatus::Safe : v::SafetyStatus::Unsafe));
        if (shortest < 0) {
            REQUIRE(answer.certificate);
            CHECK(v::CertificateSolver(decide).solve({system, *answer.certificate}).status ==
                  v::Status::Valid);
        } else {
            REQUIRE(answer.counterexample);
            CHECK(answer.counterexample->states.size() == std::size_t(shortest + 1));
            CHECK((decide(answer.counterexample->query).result == Result::Sat));
        }
    }
}
TEST_CASE("SV safety: unknown, scope and resource failures cannot become safety claims") {
    ArithmeticSystem a;
    auto system = a.system();
    DecisionOracle unknown = [](const NativeAssertions &) {
        SolverAnswer r;
        r.reason = "incomplete backend";
        return r;
    };
    auto answer = v::SafetySolver(unknown).solve({system, {a.nonnegative(a.x)}});
    CHECK(answer.status == v::SafetyStatus::Unknown);
    CHECK_FALSE(answer.certificate);
    DecisionOracle throwing = [](const NativeAssertions &) -> SolverAnswer {
        throw std::runtime_error("oracle resource exhausted");
    };
    auto failed = v::Solver(throwing).solve({{{"exception", {}, system.safety}}});
    CHECK(failed.status == v::Status::Unknown);
    CHECK(failed.reason == "oracle resource exhausted");
    CHECK(v::SafetySolver(throwing).solve({system, {}}).status == v::SafetyStatus::Unknown);
    CHECK(v::SafetySolver(decide, {3, 1, 10}).solve({system, {}}).status ==
          v::SafetyStatus::Unknown);
    CHECK(v::SafetySolver(decide, {3, 2000000, 1}).solve({system, {}}).status ==
          v::SafetyStatus::Unknown);
    system.safety = a.nonnegative(a.xp);
    CHECK(v::SafetySolver(decide).solve({system, {}}).status == v::SafetyStatus::InvalidInput);
    system.safety = a.b.logical(native::K::NT_SEP_EMP, {});
    CHECK(v::SafetySolver(decide).solve({system, {}}).status == v::SafetyStatus::InvalidInput);
    system = a.system();
    system.inputs = {a.x};
    CHECK(v::SafetySolver(decide).solve({system, {}}).status == v::SafetyStatus::InvalidInput);
}
TEST_CASE("SV safety: finite completion excludes cycles without assuming the property") {
    native::Nodes b({});
    auto x = b.make(b.bvSort(2), native::K::NT_VAR, {}, "x");
    auto xp = b.make(b.bvSort(2), native::K::NT_VAR, {}, "xp");
    auto zero = b.bv(0, 2), one = b.bv(1, 2), two = b.bv(2, 2);
    v::TransitionSystem s;
    s.state = {{x, xp}};
    s.initial = {b.equal(x, zero)};
    s.transition = {b.any({b.all({b.equal(x, zero), b.equal(xp, one)}),
                           b.all({b.equal(x, one), b.equal(xp, zero)})})};
    s.safety = b.negate(b.equal(x, two));
    auto answer = v::SafetySolver(decide, {2}, v::SafetyMethod::Bounded).solve({s, {}});
    REQUIRE(answer.status == v::SafetyStatus::Safe);
    REQUIRE(answer.certificate);
    CHECK(answer.certificate->kind == v::SafetyProof::ReachabilityDiameter);
    CHECK(answer.certificate->depth == 2);
    CHECK(v::CertificateSolver(decide).solve({s, *answer.certificate}).status == v::Status::Valid);
    auto forged = *answer.certificate;
    forged.depth = 1;
    CHECK(v::CertificateSolver(decide).solve({s, forged}).status == v::Status::Invalid);
}
