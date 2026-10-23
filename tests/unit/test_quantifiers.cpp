#include <doctest/doctest.h>
#include "applications/smt/Solver.h"
#include "quantifiers/boolean/Diagram.h"
#include "quantifiers/bitvector/Circuit.h"
#include <somtparser/frontend/parser.h>

using namespace xolver;
namespace {
SolverAnswer quantified(const std::string& text, quantifiers::Limits limits = {}) {
    SOMTParser::Parser parser;
    if (!parser.parseStr("(set-logic ALL)" + text)) throw std::runtime_error("quantifier test input did not parse");
    applications::smt::Solver solver({});
    return solver.solve({parser.getAssertions(), {}, {}, limits});
}
void cases(const std::vector<std::pair<std::string, Result>>& inputs) {
    for (const auto& [formula, expected] : inputs) {
        INFO(formula);
        auto answer = quantified("(assert " + formula + ")");
        INFO(answer.reason);
        CHECK(answer.result == expected);
    }
}
}
TEST_CASE("quantifiers: BDD quantification agrees with every three-variable truth table") {
    using D = quantifiers::boolean::Diagram;
    for (unsigned table = 0; table < 256; ++table) {
        quantifiers::Resources resources;
        D diagram(resources);
        const auto a = diagram.variable(), b = diagram.variable(), c = diagram.variable();
        D::Id root = 0;
        for (unsigned mask = 0; mask < 8; ++mask) {
            if (!(table & (1u << mask))) continue;
            D::Id cube = 1;
            for (unsigned i = 0; i < 3; ++i) {
                auto variable = i == 0 ? a : i == 1 ? b : c;
                cube = diagram.conjunction(cube, mask & (1u << i) ? variable : diagram.negate(variable));
            }
            root = diagram.disjunction(root, cube);
        }
        for (unsigned prefix = 0; prefix < 8; ++prefix) {
            auto expected = [&](auto&& self, unsigned level, unsigned mask) -> bool {
                if (level == 3) return table & (1u << mask);
                const bool x = self(self, level + 1, mask), y = self(self, level + 1, mask | (1u << level));
                return prefix & (1u << level) ? x && y : x || y;
            };
            auto value = root;
            for (unsigned i = 3; i-- > 0;)
                value = diagram.eliminate(value, {diagram.variableOf(i == 0 ? a : i == 1 ? b : c)}, prefix & (1u << i));
            CHECK(value == unsigned(expected(expected, 0, 0)));
        }
        if (root) CHECK(diagram.evaluate(root, diagram.witness(root)));
    }
}
TEST_CASE("quantifiers: finite arithmetic agrees with exhaustive modular integers") {
    quantifiers::Resources resources({.work = 0});
    quantifiers::boolean::Diagram diagram(resources);
    quantifiers::bitvector::Circuit circuit(diagram);
    const auto number = [](const quantifiers::bitvector::Word& word) {
        unsigned n = 0;
        for (unsigned i = 0; i < word.size(); ++i) { CHECK(word[i] <= 1); n |= word[i] << i; }
        return n;
    };
    for (unsigned a = 0; a < 16; ++a) for (unsigned b = 0; b < 16; ++b) {
        const auto x = circuit.constant(a, 4), y = circuit.constant(b, 4);
        CHECK(number(circuit.add(x, y)) == ((a + b) & 15));
        CHECK(number(circuit.subtract(x, y)) == ((a - b) & 15));
        CHECK(number(circuit.multiply(x, y)) == ((a * b) & 15));
        const auto [q, r] = circuit.divide(x, y);
        CHECK(number(q) == (b ? a / b : 15));
        CHECK(number(r) == (b ? a % b : a));
        CHECK(number(circuit.shift(x, y, true, false)) == (b >= 4 ? 0 : (a << b) & 15));
        CHECK(number(circuit.shift(x, y, false, false)) == (b >= 4 ? 0 : a >> b));
        const int sa = a < 8 ? int(a) : int(a) - 16;
        const int sb = b < 8 ? int(b) : int(b) - 16;
        CHECK(circuit.less(x, y, true) == unsigned(sa < sb));
        CHECK(number(circuit.shift(x, y, false, true)) == unsigned((sa >> (b >= 4 ? 4 : b)) & 15));
    }
}
TEST_CASE("quantifiers: QBF alternation and scope") {
    cases({
        {"(forall ((x Bool)) (exists ((y Bool)) (= x y)))", Result::Sat},
        {"(exists ((y Bool)) (forall ((x Bool)) (= x y)))", Result::Unsat},
        {"(forall ((x Bool)) (exists ((x Bool)) x))", Result::Sat},
        {"(not (exists ((x Bool)) (and x (not x))))", Result::Sat},
        {"(forall ((x Bool)) (let ((y (not x))) (xor x y)))", Result::Sat},
        {"(= (exists ((x Bool)) x) (forall ((x Bool)) x))", Result::Unsat},
        {"(forall ((x Bool)) (ite x (exists ((y Bool)) y) (not x)))", Result::Sat},
        {"(forall ((x Bool)) true)", Result::Sat}});
    auto model = quantified("(declare-const x Bool)(assert x)(assert (exists ((x Bool)) (not x)))");
    REQUIRE(model.result == Result::Sat);
    REQUIRE(model.model);
    CHECK(model.model->assignments.at("x") == "true");
}
TEST_CASE("quantifiers: native fixed-width operators and alternating binders") {
    cases({
        {"(forall ((x (_ BitVec 4))) (exists ((y (_ BitVec 4))) (= (bvadd x y) #xf)))", Result::Sat},
        {"(exists ((y (_ BitVec 3))) (forall ((x (_ BitVec 3))) (= (bvadd x y) #b000)))", Result::Unsat},
        {"(forall ((x (_ BitVec 4))) (= (bvudiv x #x0) #xf))", Result::Sat},
        {"(forall ((x (_ BitVec 4))) (= (bvurem x #x0) x))", Result::Sat},
        {"(= (bvsdiv #x8 #xf) #x8)", Result::Sat},
        {"(= (bvsdiv #x9 #x0) #x1)", Result::Sat},
        {"(= (bvsdiv #x7 #x0) #xf)", Result::Sat},
        {"(= (bvsmod #x9 #x3) #x2)", Result::Sat},
        {"(= (bvsrem #x9 #x3) #xf)", Result::Sat},
        {"(= ((_ extract 5 2) (concat #xa #x5)) #x9)", Result::Sat},
        {"(= ((_ sign_extend 4) #x8) #xf8)", Result::Sat},
        {"(= ((_ zero_extend 4) #x8) #x08)", Result::Sat},
        {"(= ((_ repeat 2) #xa) #xaa)", Result::Sat},
        {"(= ((_ rotate_left 1) #x9) #x3)", Result::Sat},
        {"(= ((_ rotate_right 1) #x9) #xc)", Result::Sat},
        {"(forall ((x (_ BitVec 128))) (= (bvxor x x) (_ bv0 128)))", Result::Sat},
        {"(forall ((x (_ BitVec 4))) (= (bvadd x (_ bv1 4)) x))", Result::Unsat}});
    auto model = quantified("(declare-const x (_ BitVec 4))(assert (= (bvadd x #x1) #x0))");
    REQUIRE(model.result == Result::Sat);
    REQUIRE(model.model);
    CHECK(model.model->assignments.at("x") == "(_ bv15 4)");
}
TEST_CASE("quantifiers: real closed fields and degree drops") {
    cases({
        {"(forall ((x Real)) (exists ((y Real)) (> y x)))", Result::Sat},
        {"(exists ((y Real)) (forall ((x Real)) (> y x)))", Result::Unsat},
        {"(forall ((x Real)) (>= (* x x) 0))", Result::Sat},
        {"(forall ((x Real)) (exists ((y Real)) (= (* y y) (+ (* x x) 1))))", Result::Sat},
        {"(forall ((x Real)) (exists ((y Real)) (= (* y y) x)))", Result::Unsat},
        {"(exists ((x Real)) (and (> x 0) (= (* x x) 2) (exists ((y Real)) (= (* y y) x))))", Result::Sat},
        {"(forall ((a Real)) (exists ((x Real)) (= (+ (* a x x) x) 0)))", Result::Sat},
        {"(forall ((a Real)) (exists ((x Real)) (= (+ (* a x x) 1) 0)))", Result::Unsat},
        {"(exists ((a Real)) (and (= a 0) (forall ((x Real)) (= (* a x x) 0))))", Result::Sat},
        {"(forall ((a Real)) (exists ((b Bool)) (= b (> a 0))))", Result::Sat},
        {"(exists ((b Bool)) (forall ((a Real)) (= b (> a 0))))", Result::Unsat},
        {"(forall ((x Real)) (= (ite (> x 0) x (- x)) (abs x)))", Result::Sat},
        {"(not (exists ((x Real)) (< (abs x) 0)))", Result::Sat},
        {"(forall ((x Real)) (= (exists ((y Real)) (> y x)) true))", Result::Sat},
        {"(forall ((x Real)) (exists ((y Real)) (and (< x y) (< y (+ x (/ 1 17))))))", Result::Sat}});
    auto model = quantified("(declare-const a Real)(assert (and (> a 0) (= (* a a) 2)))"
                            "(assert (forall ((x Real)) (>= (* x x) 0)))");
    INFO(model.reason);
    REQUIRE(model.result == Result::Sat);
    REQUIRE(model.model);
    CHECK(model.model->numericAssignments.at("a").isAlgebraic());
}
TEST_CASE("quantifiers: budgets stop computation without a logical verdict") {
    for (const auto& formula : {"(forall ((x Bool)) (or x (not x)))", "(forall ((x Real)) (>= (* x x) 0))"}) {
        auto answer = quantified(std::string("(assert ") + formula + ")", {.work = 2});
        CHECK(answer.result == Result::Unknown);
        CHECK(answer.reason.find("budget") != std::string::npos);
    }
}
