#include "applications/smt/Solver.h"
#include "frontend/parser/NativeTheoryPolicy.h"
#include "ir/NativeBuilder.h"
#include "search/arith/IntegerBounds.h"
#include <doctest/doctest.h>
#include <functional>
#include <somtparser/frontend/parser.h>

using namespace xolver;
TEST_CASE("SMT ranges: standard dispatch proves variable-divisor bounds") {
    SOMTParser::Parser parser;
    preserveNativeTheories(*parser.getOptions());
    REQUIRE(
        parser.parseStr("(set-logic ALL)(declare-const x Int)(declare-const y Int)"
                        "(assert (>= x (- 9)))(assert (<= x 9))(assert (>= y (- 5)))"
                        "(assert (<= y 5))(assert (not (= y 0)))"
                        "(assert (not (<= (ite (= y 0) x (ite (< x 0)"
                        "(- (mod (ite (< x 0) (- x) x) y)) (mod (ite (< x 0) (- x) x) y))) 4)))"));
    auto roots = parser.getAssertions();
    bool groundCalled = false;
    applications::smt::Solver solver([&](const applications::smt::Problem &) {
        groundCalled = true;
        return SolverAnswer{};
    });
    CHECK((solver.solve({roots, {}, {}, {}}).result == Result::Unsat));
    CHECK_FALSE(groundCalled);
    auto proof = integer_bounds::refute(roots);
    REQUIRE(proof.status == integer_bounds::ProofStatus::Proved);
    REQUIRE(proof.certificate);
    native::Nodes nodes(roots);
    CHECK(integer_bounds::check(roots, nodes.boolean(false), *proof.certificate).status ==
          integer_bounds::ProofStatus::Proved);
}
TEST_CASE("SMT ranges: nonlinear machine bounds use the shared arithmetic proof") {
    SOMTParser::Parser parser;
    preserveNativeTheories(*parser.getOptions());
    REQUIRE(parser.parseStr("(set-logic QF_NIA)(declare-const a Int)(declare-const b Int)"
                            "(assert (and (<= (- 2147483648) a) (<= a 2147483647)"
                            "(<= (- 2147483648) b) (<= b 2147483647)))"
                            "(assert (not (and (<= (* a b) 9223372036854775807)"
                            "(<= (- 9223372036854775808) (* a b)))))"));
    CHECK((applications::smt::Solver().solve({parser.getAssertions(), {}, {}, {}}).result ==
           Result::Unsat));
}
TEST_CASE("SMT ranges: an open proof preserves the original ground query") {
    SOMTParser::Parser parser;
    preserveNativeTheories(*parser.getOptions());
    REQUIRE(parser.parseStr("(set-logic QF_NIA)(declare-const x Int)(declare-const y Int)"
                            "(assert (and (<= 0 x) (<= x 5) (<= 0 y) (<= y 5)))"
                            "(assert (> (* x y) 10))"));
    auto roots = parser.getAssertions();
    bool called = false;
    applications::smt::Solver solver([&](const applications::smt::Problem &p) {
        CHECK(p.assertions == roots);
        called = true;
        SolverAnswer answer;
        answer.result = Result::Sat;
        return answer;
    });
    CHECK((solver.solve({roots, {}, {}, {}}).result == Result::Sat));
    CHECK(called);
    CHECK(integer_bounds::refute(roots).status == integer_bounds::ProofStatus::Open);
}
TEST_CASE("SMT ranges: mandatory negations can refute but disjuncts cannot supply bounds") {
    native::Nodes b({});
    auto x = b.make(SOMTParser::SortManager::getInt(), native::K::NT_VAR, {}, "x");
    auto lower = b.logical(native::K::NT_GE, {x, b.numeral(0)});
    CHECK(integer_bounds::refute({lower, b.negate(lower)}).status ==
          integer_bounds::ProofStatus::Proved);
    auto upper = b.logical(native::K::NT_LE, {x, b.numeral(2)});
    auto product = b.make(x->getSort(), native::K::NT_MUL, {x, x});
    CHECK(integer_bounds::refute(
              {b.any({lower, upper}), b.logical(native::K::NT_GT, {product, b.numeral(4)})})
              .status == integer_bounds::ProofStatus::Open);
}

TEST_CASE("SMT ranges: expression bounds retain differences and check their sources") {
    SOMTParser::Parser parser;
    preserveNativeTheories(*parser.getOptions());
    REQUIRE(parser.parseStr("(set-logic QF_NIA)(declare-const a Int)(declare-const b Int)"
                            "(declare-const c Int)(declare-const d Int)"
                            "(assert (and (<= (- 2) a) (<= a 2) (<= (- 2) b) (<= b 2)"
                            "(<= (- 2) c) (<= c 2) (<= (- 2) d) (<= d 2)))"
                            "(assert (>= (- a b) 0))(assert (> (- c d) 0))"
                            "(assert (< (* (- a b) (- c d)) 0))"));
    auto roots = parser.getAssertions();
    auto proof = integer_bounds::refute(roots);
    REQUIRE(proof.status == integer_bounds::ProofStatus::Proved);
    REQUIRE(proof.certificate);
    REQUIRE_FALSE(proof.certificate->terms.empty());
    native::Nodes nodes(roots);
    CHECK(integer_bounds::check(roots, nodes.boolean(false), *proof.certificate).status ==
          integer_bounds::ProofStatus::Proved);
    auto forged = *proof.certificate;
    auto &entry = forged.terms.front();
    if (entry.lower)
        ++*entry.lower;
    else
        --*entry.upper;
    CHECK(integer_bounds::check(roots, nodes.boolean(false), forged).status ==
          integer_bounds::ProofStatus::Invalid);
}

TEST_CASE("SMT ranges: checked refutations agree with exhaustive bounded integers") {
    native::Nodes b({});
    using K = native::K;
    auto sort = SOMTParser::SortManager::getInt();
    auto integer = [&](int value) { return b.make(sort, K::NT_CONST, {}, std::to_string(value)); };
    auto x = b.make(sort, K::NT_VAR, {}, "x");
    auto y = b.make(sort, K::NT_VAR, {}, "y");
    auto zero = b.numeral(0);
    auto lessZero = b.logical(K::NT_LT, {x, zero});
    struct Term {
        native::Node node;
        std::function<int(int, int)> evaluate;
        bool excludesZero = false;
    };
    // Independent small-integer definitions of Euclidean quotient/remainder.
    auto rem = [](int a, int d) {
        int magnitude = d < 0 ? -d : d;
        return (a % magnitude + magnitude) % magnitude;
    };
    std::vector<Term> terms{{b.make(sort, K::NT_MUL, {x, y}), [](int a, int c) { return a * c; }},
                            {b.make(sort, K::NT_MUL, {x, x}), [](int a, int) { return a * a; }},
                            {b.make(sort, K::NT_ITE, {lessZero, b.make(sort, K::NT_NEG, {x}), x}),
                             [](int a, int) { return a < 0 ? -a : a; }},
                            {b.make(sort, K::NT_MOD, {x, y}), rem, true},
                            {b.make(sort, K::NT_DIV_INT, {x, y}),
                             [rem](int a, int d) { return (a - rem(a, d)) / d; }, true}};
    for (int exponent = 0; exponent <= 5; ++exponent)
        terms.push_back({b.make(sort, K::NT_POW, {x, b.numeral(exponent)}), [exponent](int a, int) {
                             int value = 1;
                             for (int i = 0; i < exponent; ++i)
                                 value *= a;
                             return value;
                         }});
    std::size_t proved = 0, open = 0;
    for (const auto &term : terms)
        for (int threshold = -5; threshold <= 5; ++threshold)
            for (int restriction = 0; restriction < 5; ++restriction)
                for (auto kind : {K::NT_LE, K::NT_LT, K::NT_EQ, K::NT_DISTINCT}) {
                    NativeAssertions assertions{b.logical(K::NT_GE, {x, integer(-2)}),
                                                b.logical(K::NT_LE, {x, b.numeral(2)}),
                                                b.logical(K::NT_GE, {y, integer(-2)}),
                                                b.logical(K::NT_LE, {y, b.numeral(2)})};
                    if (term.excludesZero)
                        assertions.push_back(b.logical(K::NT_DISTINCT, {y, zero}));
                    if (restriction == 1 || restriction == 2)
                        assertions.push_back(
                            b.logical(restriction == 1 ? K::NT_GE : K::NT_EQ,
                                      {term.node, integer(restriction == 1 ? 0 : 1)}));
                    if (restriction >= 3)
                        assertions.push_back(b.logical(K::NT_DISTINCT, {term.node, zero}));
                    if (restriction == 4)
                        assertions.push_back(b.logical(K::NT_LE, {term.node, zero}));
                    assertions.push_back(b.logical(kind, {term.node, integer(threshold)}));
                    bool satisfiable = false;
                    for (int a = -2; a <= 2; ++a)
                        for (int d = -2; d <= 2; ++d) {
                            if (term.excludesZero && !d)
                                continue;
                            int value = term.evaluate(a, d);
                            if ((restriction == 1 && value < 0) || (restriction == 2 && value != 1))
                                continue;
                            if ((restriction >= 3 && value == 0) || (restriction == 4 && value > 0))
                                continue;
                            satisfiable |= kind == K::NT_LE   ? value <= threshold
                                           : kind == K::NT_LT ? value < threshold
                                           : kind == K::NT_EQ ? value == threshold
                                                              : value != threshold;
                        }
                    auto proof = integer_bounds::refute(assertions);
                    CAPTURE(threshold);
                    CAPTURE(static_cast<int>(kind));
                    REQUIRE(proof.status != integer_bounds::ProofStatus::Invalid);
                    if (proof.status == integer_bounds::ProofStatus::Proved) {
                        ++proved;
                        CHECK_FALSE(satisfiable);
                        REQUIRE(proof.certificate);
                        CHECK(
                            integer_bounds::check(assertions, b.boolean(false), *proof.certificate)
                                .status == integer_bounds::ProofStatus::Proved);
                    } else
                        ++open;
                }
    CHECK(proved > 0);
    CHECK(open > 0);
}
