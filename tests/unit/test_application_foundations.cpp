#include "applications/counting/Solver.h"
#include "applications/cp/Solver.h"
#include "applications/de/ode/Solver.h"
#include "applications/milp/Solver.h"
#include "applications/omt/Optimize.h"
#include "applications/smt/Solver.h"
#include "applications/sv/verification/Solver.h"
#include "ir/NativeBuilder.h"
#include "search/optimization/LinearProgram.h"
#include <doctest/doctest.h>
#include <somtparser/frontend/parser.h>

using namespace xolver;
namespace {
SOMTParser::Node symbol(SOMTParser::Parser &p, const std::string &name) {
    for (auto n : p.getDeclaredVariables())
        if (n->getName() == name)
            return n;
    throw std::runtime_error("missing variable");
}
DecisionOracle oracle = [](const NativeAssertions &q) {
    return applications::smt::Solver().solve({q, {}, {}, {}});
};
} // namespace
TEST_CASE("application foundations: exact LP feasibility, free variables and recession rays") {
    using namespace optimization;
    WorkBudget budget;
    LinearProgram p{2, {{{1, 1}, 3}, {{-1, 0}, -1}, {{0, -1}, -1}}, {1, 2}, 0, true};
    auto r = solveLinear(p, budget);
    REQUIRE(r.status == Status::Optimal);
    CHECK((*r.value == 5));
    CHECK((r.point == std::vector<mpq_class>{1, 2}));
    p.constraints = {{{1, -1}, 0}, {{-1, 1}, 0}};
    r = solveLinear(p, budget);
    REQUIRE(r.status == Status::Unbounded);
    CHECK((r.ray[0] + 2 * r.ray[1] > 0));
    p.constraints = {{{1, 0}, -2}, {{-1, 0}, 1}};
    CHECK(solveLinear(p, budget).status == Status::Infeasible);
    p.constraints = {{{1, -1}, 0}, {{-1, 1}, 0}, {{1, 0}, 2}};
    p.objective = {1, -1};
    CHECK((*solveLinear(p, budget).value == 0));
}
TEST_CASE(
    "application foundations: mixed optimization agrees with independent interval enumeration") {
    using namespace applications::milp;
    unsigned state = 431;
    auto random = [&]() {
        state = state * 1664525u + 1013904223u;
        return int((state >> 16) % 7) - 3;
    };
    for (int sample = 0; sample < 80; ++sample) {
        INFO(sample);
        Problem p;
        p.variables = {{"x", VariableKind::Integer, -2, 3},
                       {"y", VariableKind::Integer, -2, 3},
                       {"z", VariableKind::Continuous, -2, 4}};
        p.objective = {random(), random(), random()};
        p.objectiveOffset = mpq_class(random(), 2);
        p.maximize = sample % 2;
        for (int i = 0; i < 4; ++i)
            p.constraints.push_back(
                {{random(), random(), random()}, Relation::LessEqual, random()});
        std::optional<mpq_class> expected;
        for (int x = -2; x <= 3; ++x)
            for (int y = -2; y <= 3; ++y) {
                mpq_class lo = -2, hi = 4;
                bool feasible = true;
                for (const auto &c : p.constraints) {
                    mpq_class rhs = c.rhs - c.coefficients[0] * x - c.coefficients[1] * y;
                    if (c.coefficients[2] == 0) {
                        if (rhs < 0)
                            feasible = false;
                    } else if (c.coefficients[2] > 0)
                        hi = std::min(hi, mpq_class(rhs / c.coefficients[2]));
                    else
                        lo = std::max(lo, mpq_class(rhs / c.coefficients[2]));
                }
                if (!feasible || lo > hi)
                    continue;
                mpq_class z = ((p.objective[2] > 0) == p.maximize) ? hi : lo;
                mpq_class value = p.objectiveOffset + p.objective[0] * x + p.objective[1] * y +
                                  p.objective[2] * z;
                if (!expected || (p.maximize ? value > *expected : value < *expected))
                    expected = value;
            }
        auto r = Solver().solve(p);
        INFO(r.reason);
        if (!expected) {
            CHECK(r.status == Status::Infeasible);
            continue;
        }
        REQUIRE(r.status == Status::Optimal);
        REQUIRE(r.objectiveValue);
        CHECK((*r.objectiveValue == *expected));
        REQUIRE(r.assignment.size() == 3);
        CHECK((r.assignment[0].get_den() == 1));
        CHECK((r.assignment[1].get_den() == 1));
    }
}
TEST_CASE("application foundations: arithmetic OMT strict bounds, disjunctions and lexicographic "
          "values") {
    using namespace applications::omt;
    auto solve = [](const std::string &constraint, bool integer = false) {
        SOMTParser::Parser p;
        REQUIRE(p.parseStr("(set-logic ALL)(declare-const x " +
                           std::string(integer ? "Int" : "Real") + ")(assert " + constraint + ")"));
        return Solver().solve({p.getAssertions(),
                               {{symbol(p, "x"), Direction::Minimize, Order::Arithmetic}},
                               Priority::Lexicographic,
                               {}});
    };
    auto r = solve("(> x 0)");
    INFO(r.reason);
    CHECK(r.status == Status::InfimumNotAttained);
    REQUIRE(r.objectiveValues.size() == 1);
    CHECK((r.objectiveValues[0] == RealValue::fromInt(0)));
    r = solve("(> x 0)", true);
    REQUIRE(r.status == Status::Optimal);
    CHECK((r.objectiveValues[0] == RealValue::fromInt(1)));
    CHECK(solve("(< x 0)").status == Status::Unbounded);
    CHECK(solve("(and (> x 0) (<= x 0))").status == Status::Infeasible);
    r = solve("(or (> x 0) (= x 0))");
    CHECK(r.status == Status::Optimal);
    SOMTParser::Parser p;
    REQUIRE(p.parseStr("(set-logic ALL)(declare-const x Real)(declare-const y Real)(assert (= (+ x "
                       "y) 3))(assert (>= x 0))(assert (>= y 0))"));
    r = Solver().solve({p.getAssertions(),
                        {{symbol(p, "x"), Direction::Maximize, Order::Arithmetic},
                         {symbol(p, "y"), Direction::Minimize, Order::Arithmetic}},
                        Priority::Lexicographic,
                        {}});
    INFO(r.reason);
    REQUIRE(r.status == Status::Optimal);
    CHECK((r.objectiveValues ==
           std::vector<RealValue>{RealValue::fromInt(3), RealValue::fromInt(0)}));
}
TEST_CASE("application foundations: projected integer counts, overlap and infinite domains") {
    using namespace applications::counting;
    SOMTParser::Parser p;
    REQUIRE(p.parseStr("(set-logic ALL)(declare-const x Int)(declare-const y Int)(assert (or (and "
                       "(>= x 0) (<= x 3)) (= x 2)))(assert (= y (* 2 x)))"));
    auto r = Solver().solve({p.getAssertions(), {symbol(p, "x")}, {}});
    INFO(r.reason);
    REQUIRE(r.status == Status::Exact);
    CHECK((r.count == 4));
    r = Solver().solve({p.getAssertions(), {symbol(p, "x"), symbol(p, "y")}, {}});
    REQUIRE(r.status == Status::Exact);
    CHECK((r.count == 4));
    r = Solver().solve({{}, {symbol(p, "x")}, {}});
    CHECK(r.status == Status::Infinite);
    r = Solver().solve({p.getAssertions(), {}, {}});
    CHECK(r.status == Status::Exact);
    CHECK((r.count == 1));
}
TEST_CASE("application foundations: mixed integer-real SMT and CP global constraints") {
    SOMTParser::Parser p;
    REQUIRE(p.parseStr("(set-logic ALL)(declare-const x Int)(declare-const r Real)(assert (= "
                       "(to_real x) r))(assert (> r 0))(assert (< r 1))"));
    CHECK((oracle(p.getAssertions()).result == Result::Unsat));
    native::Nodes b({});
    auto ints = SOMTParser::SortManager::getInt();
    auto x = b.make(ints, native::K::NT_VAR, {}, "x"), y = b.make(ints, native::K::NT_VAR, {}, "y");
    applications::cp::Problem cp;
    cp.tables = {{{x, y}, {{b.numeral(0), b.numeral(2)}, {b.numeral(1), b.numeral(3)}}, true}};
    cp.elements = {{x, y, {b.numeral(2), b.numeral(3)}, 0}};
    auto decide = applications::cp::Solver(oracle);
    CHECK((decide.solve(cp).result == Result::Sat));
    cp.tables.push_back({{x}, {{b.numeral(0)}, {b.numeral(1)}}, false});
    CHECK((decide.solve(cp).result == Result::Unsat));
    cp = {};
    auto a = b.make(SOMTParser::SortManager::getBool(), native::K::NT_VAR, {}, "a");
    cp.cardinalities = {{{a, b.negate(a)}, 1, 1}};
    CHECK((decide.solve(cp).result == Result::Sat));
    cp.cardinalities[0].lower = 2;
    CHECK((decide.solve(cp).result == Result::Unsat));
}
TEST_CASE(
    "application foundations: inductive invariants distinguish induction and safety failures") {
    using namespace applications::sv::verification;
    native::Nodes b({});
    auto ints = SOMTParser::SortManager::getInt();
    auto x = b.make(ints, native::K::NT_VAR, {}, "x"),
         xp = b.make(ints, native::K::NT_VAR, {}, "next_x");
    auto nonnegative = b.logical(native::K::NT_GE, {x, b.numeral(0)});
    TransitionSystem p;
    p.state = {{x, xp}};
    p.initial = {b.equal(x, b.numeral(0))};
    p.transition = {b.equal(xp, b.make(ints, native::K::NT_ADD, {x, b.numeral(1)}))};
    p.invariant = p.safety = nonnegative;
    InvariantSolver solver(oracle);
    CHECK(solver.solve(p).status == Status::Valid);
    p.safety = b.logical(native::K::NT_LE, {x, b.numeral(5)});
    auto r = solver.solve(p);
    CHECK(r.status == Status::Invalid);
    CHECK(r.obligation == 2);
    p.safety = nonnegative;
    p.transition = {b.equal(xp, b.make(ints, native::K::NT_SUB, {x, b.numeral(1)}))};
    r = solver.solve(p);
    CHECK(r.status == Status::Invalid);
    CHECK(r.obligation == 1);
    p.invariant = b.equal(xp, b.numeral(0));
    CHECK(solver.solve(p).status == Status::InvalidInput);
}
TEST_CASE("application foundations: polynomial ODE solutions depend on declared parameters") {
    using namespace applications::de;
    native::Nodes b({});
    auto reals = SOMTParser::SortManager::getReal();
    auto var = [&](const char *name) { return b.make(reals, native::K::NT_VAR, {}, name); };
    auto t = var("t"), a = var("a"), dy = var("dy"), y0 = var("y0");
    auto zero = b.make(reals, native::K::NT_CONST, {}, "0");
    Problem p{{t},
              {a},
              {"y"},
              {{dy, 0, {1}, {}}, {y0, 0, {0}, {zero}}},
              {{{}, b.equal(dy, a)}, {{}, b.equal(y0, zero)}}};
    auto r = ode::Solver({2, 128, {}}).solve(p);
    INFO(r.reason);
    REQUIRE(r.status == Status::Solved);
    CHECK((oracle({b.negate(b.equal(r.functions[0], b.make(reals, native::K::NT_MUL, {a, t})))})
               .result == Result::Unsat));
}
