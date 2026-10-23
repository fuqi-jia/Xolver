#include "applications/counting/Solver.h"
#include "applications/cp/Solver.h"
#include "applications/de/ode/Solver.h"
#include "applications/de/pde/Solver.h"
#include "applications/milp/Solver.h"
#include "applications/omt/Optimize.h"
#include "applications/smt/Solver.h"
#include "applications/smt/qfbv/Solver.h"
#include "applications/sv/verification/Solver.h"
#include "ir/NativeBuilder.h"
#include "quantifiers/FiniteFormula.h"
#include <doctest/doctest.h>
#include <somtparser/frontend/parser.h>

using namespace xolver;
namespace {
using Node = SOMTParser::Node;
Node symbol(SOMTParser::Parser &p, const std::string &name) {
    for (auto n : p.getDeclaredVariables())
        if (n->getName() == name)
            return n;
    throw std::runtime_error("missing declared variable");
}
DecisionOracle oracle = [](const NativeAssertions &roots) {
    return applications::smt::Solver().solve({roots, {}, {}, {}});
};
} // namespace
TEST_CASE("application prototypes: projected model counting") {
    SOMTParser::Parser p;
    REQUIRE(p.parseStr("(set-logic ALL)(declare-const a Bool)(declare-const b Bool)(declare-const "
                       "unused (_ BitVec 128))(assert (xor a b))"));
    applications::counting::Solver solver;
    auto a = symbol(p, "a"), b = symbol(p, "b"), unused = symbol(p, "unused");
    auto result = solver.solve({p.getAssertions(), {a, b}, {}});
    REQUIRE((result.status == applications::counting::Status::Exact));
    CHECK((result.count == 2));
    CHECK((solver.solve({p.getAssertions(), {a}, {}}).count == 2));
    CHECK((solver.solve({p.getAssertions(), {}, {}}).count == 1));
    CHECK((solver.solve({p.getAssertions(), {unused}, {}}).count == (mpz_class(1) << 128)));
    CHECK((solver.solve({p.getAssertions(), {a, a}, {}}).status ==
           applications::counting::Status::InvalidInput));
}
TEST_CASE("application prototypes: lexicographic bit-vector optimization") {
    using namespace applications::omt;
    SOMTParser::Parser p;
    REQUIRE(p.parseStr("(set-logic QF_BV)(declare-const x (_ BitVec 4))(declare-const y (_ BitVec "
                       "4))(assert (= (bvadd x y) #x9))"));
    auto x = symbol(p, "x"), y = symbol(p, "y");
    Solver solver;
    auto answer = solver.solve({p.getAssertions(),
                                {{x, Direction::Maximize, Order::UnsignedBitVector},
                                 {y, Direction::Maximize, Order::UnsignedBitVector}},
                                Priority::Lexicographic,
                                {}});
    REQUIRE((answer.status == Status::Optimal));
    REQUIRE(answer.objectiveValues.size() == 2);
    CHECK((answer.objectiveValues[0] == RealValue::fromInt(15)));
    CHECK((answer.objectiveValues[1] == RealValue::fromInt(10)));
    REQUIRE(answer.model);
    auto signedAnswer = solver.solve(
        {{}, {{x, Direction::Minimize, Order::SignedBitVector}}, Priority::Lexicographic, {}});
    REQUIRE((signedAnswer.status == Status::Optimal));
    CHECK((signedAnswer.objectiveValues[0] == RealValue::fromInt(-8)));
    applications::smt::qfbv::Solver satisfiable;
    CHECK((satisfiable.solve({p.getAssertions(), {}, {}, {}}).result == Result::Sat));
}
TEST_CASE("application prototypes: counts and optima agree with exhaustive assignments") {
    native::Nodes nodes({});
    auto sort = nodes.bvSort(3);
    auto x = nodes.make(sort, native::K::NT_VAR, {}, "x");
    auto y = nodes.make(sort, native::K::NT_VAR, {}, "y");
    auto sum = nodes.make(sort, native::K::NT_BV_ADD, {x, y});
    applications::counting::Solver counter;
    applications::omt::Solver optimizer;
    for (int target = 0; target < 8; ++target) {
        INFO(target);
        auto constraint = nodes.all({nodes.equal(sum, nodes.bv(target, 3)),
                                     nodes.logical(native::K::NT_BV_ULT, {y, nodes.bv(5, 3)})});
        int count = 0, minimumSignedX = 8, minimumY = 8;
        for (int a = 0; a < 8; ++a)
            for (int b = 0; b < 5; ++b)
                if ((a + b) % 8 == target) {
                    ++count;
                    const int signedX = a < 4 ? a : a - 8;
                    if (signedX < minimumSignedX || (signedX == minimumSignedX && b < minimumY)) {
                        minimumSignedX = signedX;
                        minimumY = b;
                    }
                }
        auto cardinality = counter.solve({{constraint}, {x, y}, {}});
        REQUIRE(cardinality.status == applications::counting::Status::Exact);
        CHECK((cardinality.count == count));
        auto projected = counter.solve({{constraint}, {x}, {}});
        REQUIRE(projected.status == applications::counting::Status::Exact);
        CHECK((projected.count == count)); // Each x has exactly one possible y.
        using namespace applications::omt;
        auto optimum = optimizer.solve({{constraint},
                                        {{x, Direction::Minimize, Order::SignedBitVector},
                                         {y, Direction::Minimize, Order::UnsignedBitVector}},
                                        Priority::Lexicographic,
                                        {}});
        INFO(optimum.reason);
        REQUIRE(optimum.status == Status::Optimal);
        REQUIRE(optimum.objectiveValues.size() == 2);
        CHECK(optimum.objectiveValues[0] == RealValue::fromInt(minimumSignedX));
        CHECK(optimum.objectiveValues[1] == RealValue::fromInt(minimumY));
        REQUIRE(optimum.model);
        CHECK(quantifiers::finiteValue(constraint, *optimum.model) == "true");
        CHECK(quantifiers::finiteValue(x, *optimum.model) ==
              "(_ bv" + std::to_string((minimumSignedX + 8) % 8) + " 3)");
        CHECK(quantifiers::finiteValue(y, *optimum.model) ==
              "(_ bv" + std::to_string(minimumY) + " 3)");
    }
}
TEST_CASE("application prototypes: CP domains and verification conditions") {
    native::Nodes b({});
    auto ints = SOMTParser::SortManager::getInt();
    auto x = b.make(ints, native::K::NT_VAR, {}, "x"), y = b.make(ints, native::K::NT_VAR, {}, "y");
    auto zero = b.numeral(0), one = b.numeral(1);
    applications::cp::Solver cp(oracle);
    applications::cp::Problem problem;
    problem.domains = {{x, applications::cp::Domain::Kind::Enumeration, {zero, one}, {}, {}},
                       {y, applications::cp::Domain::Kind::Enumeration, {zero, one}, {}, {}}};
    problem.allDifferent = {{x, y}};
    CHECK((cp.solve(problem).result == Result::Sat));
    problem.domains[0].values = {zero};
    problem.domains[1].values = {zero};
    CHECK((cp.solve(problem).result == Result::Unsat));
    applications::sv::verification::Solver verifier(oracle);
    auto nonnegative = b.logical(native::K::NT_GE, {x, zero}),
         positive = b.logical(native::K::NT_GT, {x, zero});
    auto valid = verifier.solve({{{"reflexive", {nonnegative}, nonnegative}}});
    CHECK((valid.status == applications::sv::verification::Status::Valid));
    auto invalid = verifier.solve({{{"strict", {nonnegative}, positive}}});
    CHECK((invalid.status == applications::sv::verification::Status::Invalid));
    CHECK(invalid.counterexample.has_value());
}
TEST_CASE("application prototypes: exact mixed-integer optimization") {
    using namespace applications::milp;
    Problem p;
    p.variables = {{"x", VariableKind::Integer, mpq_class(0), mpq_class(3)},
                   {"y", VariableKind::Continuous, mpq_class(0), mpq_class(4)}};
    p.constraints = {{{1, 1}, Relation::GreaterEqual, mpq_class(7, 2)}};
    p.objective = {1, 2};
    Solver solver;
    auto r = solver.solve(p);
    REQUIRE((r.status == Status::Optimal));
    REQUIRE(r.objectiveValue);
    CHECK((*r.objectiveValue == 4));
    CHECK((r.assignment == std::vector<mpq_class>{3, mpq_class(1, 2)}));
    p.variables[1].kind = VariableKind::Integer;
    r = solver.solve(p);
    REQUIRE((r.status == Status::Optimal));
    CHECK((*r.objectiveValue == 5));
    p.variables[0].lower = mpq_class(1, 2);
    p.variables[0].upper = mpq_class(3, 4);
    CHECK((solver.solve(p).status == Status::Infeasible));
    p.variables[0].lower.reset();
    p.variables[0].upper.reset();
    r = solver.solve(p);
    REQUIRE((r.status == Status::Optimal));
    CHECK((*r.objectiveValue == 4));
    p.variables[0].lower = 0;
    p.variables[0].upper = 3;
    p.workLimit = 1;
    CHECK((solver.solve(p).status == Status::Unknown));
}
TEST_CASE("application prototypes: ODE and PDE solutions satisfy exact identities") {
    using namespace applications::de;
    native::Nodes b({});
    auto reals = SOMTParser::SortManager::getReal();
    auto var = [&](const char *name) { return b.make(reals, native::K::NT_VAR, {}, name); };
    auto value = [&](const char *text) { return b.make(reals, native::K::NT_CONST, {}, text); };
    auto t = var("t"), dy = var("dy"), y0 = var("y0");
    Problem odeProblem{{t},
                       {},
                       {"y"},
                       {{dy, 0, {1}, {}}, {y0, 0, {0}, {value("0")}}},
                       {{{}, b.equal(dy, value("2"))}, {{}, b.equal(y0, value("1"))}}};
    ode::Solver odeSolver({1, 128, {}});
    auto result = odeSolver.solve(odeProblem);
    INFO(result.reason);
    REQUIRE((result.status == Status::Solved));
    REQUIRE(result.functions.size() == 1);
    auto expected = b.make(reals, native::K::NT_ADD,
                           {value("1"), b.make(reals, native::K::NT_MUL, {value("2"), t})});
    CHECK((oracle({b.negate(b.equal(result.functions[0], expected))}).result == Result::Unsat));
    auto x = var("x"), dx = var("dx"), dt = var("dt"), origin = var("origin");
    Problem pdeProblem{
        {x, t},
        {},
        {"u"},
        {{dx, 0, {1, 0}, {}}, {dt, 0, {0, 1}, {}}, {origin, 0, {0, 0}, {value("0"), value("0")}}},
        {{{}, b.equal(dx, value("1"))},
         {{}, b.equal(dt, value("2"))},
         {{}, b.equal(origin, value("0"))}}};
    pde::Solver pdeSolver({1, 128, {}});
    auto pdeResult = pdeSolver.solve(pdeProblem);
    INFO(pdeResult.reason);
    REQUIRE((pdeResult.status == Status::Solved));
    REQUIRE(pdeResult.functions.size() == 1);
    auto plane =
        b.make(reals, native::K::NT_ADD, {x, b.make(reals, native::K::NT_MUL, {value("2"), t})});
    CHECK((oracle({b.negate(b.equal(pdeResult.functions[0], plane))}).result == Result::Unsat));
    ode::Solver constantOnly({0, 128, {}});
    CHECK((constantOnly.solve(odeProblem).status == Status::Unknown));
}
