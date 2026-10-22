#include <doctest/doctest.h>
#include "decision/sl/NativeSeparation.h"
#include "xolver/Solver.h"
#include <somtparser/frontend/parser.h>
#include <filesystem>
#include <fstream>
#include <unistd.h>

using namespace xolver;
namespace {
const std::string header =
    "(set-logic QF_ALL)(declare-heap (Int Int))"
    "(declare-const x Int)(declare-const y Int)(declare-const p Bool)";
sl::NativeDecision solveText(const std::string& text) {
    SOMTParser::Parser parser;
    if (!parser.parseStr(text)) throw std::runtime_error("SL fixture failed to parse");
    return sl::decideNative(parser.getHeapLocationSort(), parser.getHeapDataSort(),
                            parser.getAssertions(), parser.getDeclaredVariables(), {3000000, 256});
}
}

TEST_CASE("native SL preserves Boolean and spatial semantics through the parser") {
    const std::vector<std::pair<std::string, Result>> cases = {
        {"sep.emp", Result::Sat},
        {"(pto (as sep.nil Int) 0)", Result::Unsat},
        {"(sep (pto x 1) (pto x 2))", Result::Unsat},
        {"(and (distinct x y) (pto x 1) (pto y 1))", Result::Unsat},
        {"(sep (pto x 1) (pto y 2))", Result::Sat},
        {"(and (= x 0) (pto x 7))", Result::Sat},
        {"(and (= x 0) (= (as sep.nil Int) 0) (pto x 7))", Result::Unsat},
        {"(and (distinct x y) (pto 5 x) (pto 5 y))", Result::Unsat},
        {"(and (pto x y) (= y 123456789012345678901234567890))", Result::Sat},
        {"(wand true sep.emp)", Result::Unsat},
        {"(wand (wand (not true) (pto x 1)) (pto x 1))", Result::Unsat},
        {"(and sep.emp (wand (pto x 1) (pto x 1)))", Result::Sat},
        {"(and p (ite p (pto x y) sep.emp))", Result::Sat},
        {"(and p (not (=> p (not sep.emp))) sep.emp)", Result::Sat},
        {"(and p (xor p p))", Result::Unsat},
        {"(and (= sep.emp (pto x y)) sep.emp)", Result::Unsat},
        {"(distinct sep.emp (not sep.emp))", Result::Sat},
        {"(= sep.emp true false)", Result::Unsat},
        {"(and (sep (pto 1 2) (pto 3 2)) "
         "(= (sep (not (pto 1 2)) true true) (pto 3 2)))", Result::Unsat},
        {"(let ((a (pto x y))) (and a (not a)))", Result::Unsat},
        {"(let ((x 4) (y x)) (and (distinct y 4) (pto x y)))", Result::Sat},
    };
    for (const auto& [formula, expected] : cases) {
        CAPTURE(formula);
        auto decision = solveText(header + "(assert " + formula + ")(check-sat)");
        INFO(decision.reason);
        REQUIRE((decision.result == expected));
        if (decision.result == Result::Sat) {
            REQUIRE(decision.model);
            CHECK(sl::checkInterpretation(*decision.model, {3000000, 256}).holds == std::optional<bool>(true));
        }
    }
}

TEST_CASE("native SL exports exact integers and rejects altered model components") {
    auto answer = solveText(header +
        "(assert (= (as sep.nil Int) 17))"
        "(assert (pto 0 (- 123456789012345678901234567890)))"
        "(assert (= x 0))(assert (= y (- 123456789012345678901234567890)))"
        "(assert p)(check-sat)");
    INFO(answer.reason);
    REQUIRE((answer.result == Result::Sat));
    REQUIRE(answer.model);
    CHECK(answer.model->heap.nil == "17");
    CHECK(answer.model->heap.cells.at("0") == "-123456789012345678901234567890");
    CHECK(answer.model->assignments.at("x") == "0");
    CHECK(answer.model->assignments.at("p") == "true");
    for (unsigned change = 0; change != 5; ++change) {
        auto bad = *answer.model;
        if (change == 0) bad.heap.nil = "0";
        if (change == 1) bad.heap.cells.clear();
        if (change == 2) bad.assignments["x"] = "1";
        if (change == 3) bad.values[0] = "0";
        if (change == 4) bad.assignments["p"] = "false";
        CHECK(sl::checkInterpretation(bad).holds == std::optional<bool>(false));
    }
    SOMTParser::Parser parser;
    REQUIRE(parser.parseStr(header));
    for (const auto& [text, value] : std::vector<std::pair<std::string, std::string>>{
            {"(as sep.nil Int)", "17"}, {"x", "0"}, {"y", "(- 123456789012345678901234567890)"},
            {"(pto x y)", "true"}, {"sep.emp", "false"}, {"(not p)", "false"},
            {"(= x 17)", "false"}, {"(= x 1001)", "false"},
            {"(wand sep.emp (pto x y))", "true"}}) {
        CAPTURE(text);
        CHECK(sl::nativeValue(parser.mkExpr(text), *answer.model) == std::optional<std::string>(value));
    }
}

TEST_CASE("native SL parser validates heap signatures and preserves declaration lifetime") {
    for (const auto& source : std::vector<std::string>{
            "(assert sep.emp)",
            "(declare-heap (Int Int))(declare-heap (Int Int))",
            "(assert true)(declare-heap (Int Int))",
            "(push 1)(declare-heap (Int Int))",
            "(declare-heap (Int Int))(assert (pto true 0))",
            "(declare-heap (Int Int))(assert (pto 0 false))",
            "(declare-heap (Int Int))(assert (= (as sep.nil Bool) true))",
            "(declare-heap (Int Int))(assert (wand sep.emp))",
            "(declare-heap (Int Int))(assert (sep sep.emp))"}) {
        CAPTURE(source);
        SOMTParser::Parser parser;
        CHECK_FALSE(parser.parseStr("(set-logic ALL)" + source));
    }
    SOMTParser::Parser parser;
    REQUIRE(parser.parseStr("(set-logic ALL)(declare-heap (Int Int))(assert sep.emp)"
                            "(push 1)(assert (not sep.emp))(pop 1)(reset-assertions)"));
    REQUIRE(parser.getHeapLocationSort());
    CHECK(parser.getHeapLocationSort()->isInt());
    REQUIRE(parser.parseStr("(assert sep.emp)(check-sat)"));
    auto node = parser.getAssertions().at(0);
    CHECK(node->getKind() == SOMTParser::NODE_KIND::NT_SEP_EMP);
    CHECK(SOMTParser::dumpSMTLIB2(node) == "sep.emp");
    CHECK(SOMTParser::dumpSMTLIB2(parser.mkExpr("(as sep.nil Int)")) == "(as sep.nil Int)");
    REQUIRE(parser.parseStr("(reset)(set-logic ALL)(declare-heap (Bool Int))"));
    REQUIRE(parser.getHeapLocationSort());
    CHECK(parser.getHeapLocationSort()->isBool());
}

TEST_CASE("native SL refuses unsupported domains and non-PA arithmetic without a false verdict") {
    for (const auto& text : std::vector<std::string>{
            "(declare-sort L 0)(declare-heap (L Int))(assert (wand true sep.emp))",
            "(declare-heap (Bool Int))(assert (wand true sep.emp))",
            "(declare-heap (Int Int))(declare-const x Int)(assert (pto (* x x) 0))",
            "(declare-heap (Int Int))(declare-const x Int)(assert (pto (div 1 x) 0))",
            "(declare-heap (Int Int))(declare-const x Int)(assert (pto (div x 0) 0))",
            "(declare-heap (Int Int))(assert (pto (ite sep.emp 1 2) 0))"}) {
        CAPTURE(text);
        const auto result = solveText("(set-logic ALL)" + text + "(check-sat)");
        CHECK((result.result == Result::Unknown));
        CHECK_FALSE(result.reason.empty());
        CHECK_FALSE(result.model);
    }
    // A type alias retains the infinite Int domain.
    auto alias = solveText("(set-logic ALL)(define-sort L () Int)(declare-heap (L Int))"
                           "(assert (wand true sep.emp))(check-sat)");
    INFO(alias.reason);
    CHECK((alias.result == Result::Unsat));
}

TEST_CASE("native SL combines exact PA terms predicates and spatial connectives") {
    const std::vector<std::pair<std::string, Result>> cases = {
        {"(pto (+ x 1) (- y 2))", Result::Sat},
        {"(and (> x 0) (< x 1))", Result::Unsat},
        {"(and (> x 0) sep.emp)", Result::Sat},
        {"(and (= y (+ x 1)) (sep (pto x 10) (pto y 20)))", Result::Sat},
        {"(and (= y (+ x 1)) (sep (pto (+ x 1) 0) (pto y 0)))", Result::Unsat},
        {"(and (= (as sep.nil Int) 0) (= x 5) (pto (div x (- 2)) (mod x (- 2))))", Result::Sat},
        {"(and (= (as sep.nil Int) 0) (= x (- 5)) (pto (div x (- 2)) (mod x (- 2))))", Result::Sat},
        {"(and (= x (- 4)) (pto (abs x) (+ (* 3 x) 1)))", Result::Sat},
        {"(and p (= x 5) (pto (ite p (+ x 1) (- x 1)) (abs (- x 2))))", Result::Sat},
        {"(and (<= 1 x y 3) (> x y) (pto x y))", Result::Unsat},
        {"(sep (< x 0) (> x 1))", Result::Unsat},
        {"(and (= x 0) (wand (> x 0) false))", Result::Sat},
        {"(and (= x 0) (not (wand (> x 0) false)))", Result::Unsat},
        {"(and sep.emp (= (as sep.nil Int) 0) (= x 1) (= y 3)"
         " (wand (pto (+ x 1) 0) (pto y 0)))", Result::Unsat},
        {"(and sep.emp (= (as sep.nil Int) 0) (= x 1) (= y 2)"
         " (wand (pto (+ x 1) 0) (pto y 0)))", Result::Sat},
        {"(sep (pto (+ x 1) y) (> x 0))", Result::Sat},
        {"(and (= x 0) (pto (ite (> y 0) (+ x 1) (+ x 2)) (ite p 1 2)))", Result::Sat},
        {"(let ((x (+ x 1)) (y x)) (and (= x y) (pto x y)))", Result::Unsat},
        {"(and (= x 0) (pto (+ x 1) 7) (= (as sep.nil Int) 1))", Result::Unsat},
        {"(and (= x 0) (pto (+ x 1) 7) (= (as sep.nil Int) 17))", Result::Sat},
        {"(and (> x 0) (< y 0) (= p (> x y)) (not p))", Result::Unsat},
        {"(and (> x 0) (< y 0) (= p (> x y)) p (pto x y))", Result::Sat}
    };
    for (const auto& [formula, expected] : cases) {
        CAPTURE(formula);
        auto result = solveText(header + "(assert " + formula + ")(check-sat)");
        INFO(result.reason);
        REQUIRE((result.result == expected));
        if (result.model) {
            REQUIRE(result.model->arithmetic);
            CHECK(sl::checkInterpretation(*result.model, {3000000, 256}).holds == std::optional<bool>(true));
        }
    }
}

TEST_CASE("native SL solves heap independent PA quantifiers with spatial Boolean structure") {
    const std::vector<std::pair<std::string, Result>> cases = {
        {"(and (pto x 7) (forall ((i Int)) (exists ((j Int)) (> j i))))", Result::Sat},
        {"(and (pto x 7) (forall ((i Int)) (exists ((j Int)) (= (* 2 j) i))))", Result::Unsat},
        {"(and sep.emp (not (forall ((i Int)) (exists ((j Int)) (= (* 2 j) i)))))", Result::Sat},
        {"(and sep.emp (wand (forall ((i Int)) (= i i)) sep.emp))", Result::Unsat},
        {"(wand (exists ((i Int)) (and (> i 0) (< i 1))) false)", Result::Sat},
        {"(and (= x 7) (pto x (ite (forall ((b Bool)) (or b (not b))) 3 4)))", Result::Sat},
        {"(and sep.emp (= x 7) (forall ((x Int)) (= x 7)))", Result::Unsat},
        {"(and sep.emp (= x 7) (forall ((x Int)) (exists ((x Int)) (= x 7))))", Result::Sat},
        {"(and (pto x 7) (exists ((i Int)) (= i (+ (as sep.nil Int) 1))))", Result::Sat},
        {"(and sep.emp (= x 5) (forall ((i Int)) (=> (= i 3) (< i x))))", Result::Sat},
        {"(and sep.emp (= x 2) (forall ((i Int)) (=> (= i 3) (< i x))))", Result::Unsat},
    };
    for (const auto& [formula, expected] : cases) {
        INFO(formula);
        auto answer = solveText("(set-logic ALL)(declare-heap (Int Int))(declare-const x Int)"
                                "(assert " + formula + ")(check-sat)");
        INFO(answer.reason);
        CHECK((answer.result == expected));
        if (expected == Result::Sat) {
            REQUIRE(answer.model);
            CHECK_FALSE(answer.model->assignments.count("i"));
            CHECK_FALSE(answer.model->assignments.count("j"));
        }
    }
}

TEST_CASE("native SL arithmetic disjointness conditions preserve polarity and branches") {
    const auto cell = std::string("(pto (+ x 1) 0)");
    const auto same = std::string("(pto y 0)");
    const std::vector<std::pair<std::string, Result>> cases = {
        {"(sep " + cell + " " + same + ")", Result::Unsat},
        {"(not (sep " + cell + " " + same + "))", Result::Sat},
        {"(or sep.emp (sep " + cell + " " + same + "))", Result::Sat},
        {"(sep (or sep.emp " + cell + ") " + same + ")", Result::Sat},
        {"(sep (not (not " + cell + ")) " + same + ")", Result::Unsat},
        {"(sep (or " + cell + " (and p " + cell + ")) " + same + ")", Result::Unsat},
        {"(sep (not (or (not " + cell + ") p)) " + same + ")", Result::Unsat},
        {"(sep (not (and (not " + cell + ") p)) " + same + ")", Result::Sat},
        {"(and sep.emp (wand (sep " + cell + " " + same + ") false))", Result::Sat},
    };
    for (const auto& [formula, expected] : cases) {
        CAPTURE(formula);
        auto result = solveText(header + "(assert (= y (+ x 1)))"
            "(assert " + formula + ")(check-sat)");
        INFO(result.reason);
        CHECK((result.result == expected));
        if (result.model)
            CHECK(sl::checkInterpretation(*result.model, {3000000, 256}).holds == std::optional<bool>(true));
    }
}

TEST_CASE("native SL stack conditions distinguish shared heaps and pure wand antecedents") {
    const std::vector<std::pair<std::string, Result>> cases = {
        {"(and (= x 3) (= y 2) (not p) (= (as sep.nil Int) 0)"
         " (pto (+ x 2) (mod (+ x y) (- 2))) (pto (+ y 2) (mod (+ x y) (- 2))))", Result::Unsat},
        {"(and (= x 2) (= y (- 1)) p (= (as sep.nil Int) 0)"
         " (pto (+ x 2) (mod (+ x y) 2)) (wand (> x y) false))", Result::Unsat},
        {"(and (= x 3) (= y 2) (not (and (pto (+ x 2) 1) (pto (+ y 2) 1))))", Result::Sat},
        {"(and (pto (+ x 1) 7) (pto (+ x 1) 8))", Result::Unsat},
        {"(not (or (not (pto (+ x 1) 7)) (not (pto (+ x 1) 8))))", Result::Unsat},
        {"(and (pto (+ x 1) 7) (sep (pto (+ x 1) 7) (pto (+ x 2) 7)))", Result::Unsat},
        {"(or (pto (+ x 1) 7) (pto (+ x 2) 8))", Result::Sat},
        {"(and (pto (+ x 1) 7) (wand (pto (+ x 1) 7) false))", Result::Sat},
        {"(and (= x 1) (not (sep (> x 0) (< x 2))))", Result::Unsat},
        {"(and (= x (- 4)) (= y 2) sep.emp (wand (pto (+ x (- 1)) 1) (pto (+ y 0) 1)))", Result::Sat},
        {"(and (= x (- 4)) (= y 2) (= (as sep.nil Int) 0) sep.emp"
         " (wand (pto (+ x (- 1)) 1) (pto (+ y 0) 1)))", Result::Unsat},
        {"(wand (or (not sep.emp) (pto (+ x 1) 1)) (pto (+ y 1) 0))", Result::Unsat},
        {"(and (pto (+ x 1) 1) (sep (pto (+ x 1) 0) (or (pto (+ x 1) 0) true)))", Result::Unsat},
        {"(and (sep (or (pto (as sep.nil Int) 0) (pto (+ x 1) 1))"
         " (or (pto (as sep.nil Int) 0) (pto (+ x 1) 1))) (pto (+ x 1) 1))", Result::Unsat},
        {"(and (pto (+ x 1) y) (= y (+ x 1)))", Result::Sat},
        {"(and (pto (+ x 1) y) (pto (+ x 1) (+ x 1)) (distinct y (+ x 1)))", Result::Unsat},
        {"(and (= (as sep.nil Int) 0) sep.emp (wand (pto 1 (+ x 1)) (pto 1 (+ x 2))))", Result::Unsat},
        {"(and (= (as sep.nil Int) 0) sep.emp (wand (pto 1 (+ x 1)) (pto 1 y)))", Result::Sat},
    };
    for (const auto& [formula, expected] : cases) {
        CAPTURE(formula);
        SOMTParser::Parser parser;
        REQUIRE(parser.parseStr(header + "(assert " + formula + ")(check-sat)"));
        // Use the CLI's ordinary budget, not the larger fixture allowance.
        auto answer = sl::decideNative(parser.getHeapLocationSort(), parser.getHeapDataSort(),
                                      parser.getAssertions(), parser.getDeclaredVariables());
        INFO(answer.reason);
        CHECK((answer.result == expected));
        if (answer.model) CHECK(sl::checkInterpretation(*answer.model).holds == std::optional<bool>(true));
    }
}

TEST_CASE("native SL arithmetic models tie source variables to concrete heap values") {
    auto result = solveText(header + "(assert (pto (+ x 1) (ite p 7 8)))(check-sat)");
    INFO(result.reason);
    REQUIRE((result.result == Result::Sat));
    REQUIRE(result.model);
    REQUIRE(result.model->arithmetic);
    auto bad = *result.model;
    auto& evidence = bad.arithmetic->evidence;
    const auto variable = evidence.symbols.at("x");
    evidence.values.at(variable) += 1;
    bad.assignments.at("x") = evidence.values.at(variable).get_str();
    // This x occurs only inside arithmetic: neither ordinary SL bindings nor
    // heap renaming can detect the error. The independent PA check must do so.
    CHECK_FALSE(bad.bindings.count("x"));
    CHECK(sl::checkInterpretation(bad).holds == std::optional<bool>(false));
    bad = *result.model;
    bad.arithmetic->integers.erase(0);
    CHECK(sl::checkInterpretation(bad).holds == std::optional<bool>(false));
    CHECK_FALSE(sl::checkInterpretation(*result.model, {0, 256}).holds.has_value());

    auto named = solveText(header + "(declare-const @xolver.sl.0 Int)"
        "(assert (= @xolver.sl.0 4))(assert (pto (+ @xolver.sl.0 1) 7))(check-sat)");
    INFO(named.reason);
    REQUIRE((named.result == Result::Sat));
    CHECK(named.model->assignments.at("@xolver.sl.0") == "4");
    CHECK(named.model->heap.cells.at("5") == "7");
}

TEST_CASE("native SL arithmetic get-value preserves the existing stack and heap") {
    auto result = solveText(header + "(assert (= x (- 5)))(assert p)"
        "(assert (= (as sep.nil Int) 17))(assert (pto (+ x 1) (mod x (- 2))))(check-sat)");
    INFO(result.reason);
    REQUIRE((result.result == Result::Sat));
    REQUIRE(result.model);
    SOMTParser::Parser parser;
    REQUIRE(parser.parseStr(header));
    for (const auto& [term, expected] : std::vector<std::pair<std::string, std::string>>{
            {"(+ x 1)", "(- 4)"}, {"(div x (- 2))", "3"}, {"(mod x (- 2))", "1"},
            {"(abs x)", "5"}, {"(ite p (+ x 1) x)", "(- 4)"},
            {"(< x 0)", "true"}, {"(> x 0)", "false"},
            {"(pto (+ x 1) (mod x (- 2)))", "true"},
            {"(pto (+ x 2) (mod x (- 2)))", "false"},
            {"(wand sep.emp (pto (+ x 1) 1))", "true"},
            {"(+ (as sep.nil Int) 1)", "18"}}) {
        CAPTURE(term);
        CHECK(sl::nativeValue(parser.mkExpr(term), *result.model, {3000000, 256}) ==
              std::optional<std::string>(expected));
    }
}

TEST_CASE("native parser reset removes symbols scopes and stale script options") {
    SOMTParser::Parser parser;
    REQUIRE(parser.parseStr(
        "(set-logic ALL)(declare-heap (Int Int))(declare-const x Int)"
        "(assert (= x 3))(push 1)(declare-const y Bool)(assert y)"
        "(reset-assertions)(declare-const x Bool)(assert x)"));
    REQUIRE(parser.getHeapLocationSort());
    CHECK(parser.getAssertions().size() == 1);
    CHECK_FALSE(parser.pop()); // reset-assertions returned to the base level
    CHECK(parser.getAssertions().size() == 1);
    REQUIRE(parser.parseStr(
        "(reset)(set-logic ALL)(declare-heap (Bool Int))(declare-const x Int)"
        "(assert (= x 4))(check-sat)"));
    CHECK(parser.getHeapLocationSort()->isBool());
    CHECK(parser.getAssertions().size() == 1);
    CHECK_FALSE(parser.getOptions()->global_declarations);

    SOMTParser::Parser globals;
    REQUIRE(globals.parseStr(
        "(set-logic ALL)(set-option :global-declarations true)"
        "(declare-heap (Int Int))(push 1)(declare-const x Int)(pop 1)"
        "(reset-assertions)(assert (= x 5))(check-sat)"));
    CHECK(globals.getAssertions().size() == 1);
    REQUIRE(globals.parseStr(
        "(reset)(set-logic ALL)(declare-const x Bool)(assert x)(check-sat)"));
    CHECK_FALSE(globals.getOptions()->global_declarations);

    SOMTParser::Parser underflow;
    REQUIRE(underflow.parseStr("(set-logic ALL)(assert false)(push 1)(assert true)"));
    CHECK_FALSE(underflow.parseStr("(pop 2)"));
    CHECK(underflow.getAssertions().size() == 2);
    REQUIRE(underflow.pop());
    CHECK(underflow.getAssertions().size() == 1);
}

TEST_CASE("native SL public solver keeps heap models aligned with scopes and assumptions") {
    const auto path = std::filesystem::temp_directory_path() /
        ("xolver-native-sl-api-" + std::to_string(getpid()) + ".smt2");
    struct Cleanup {
        std::filesystem::path path;
        ~Cleanup() { std::error_code error; std::filesystem::remove(path, error); }
    } cleanup{path};
    {
        std::ofstream out(path);
        out << header << "(declare-const q Bool)(assert (= q (not p)))"
                        "(assert (= p sep.emp))(check-sat)";
    }
    Solver solver;
    REQUIRE(solver.parseFile(path.string()));
    auto p = solver.mkConst(solver.boolSort(), "p");
    REQUIRE((solver.checkSatAssuming({p}) == Result::Sat));
    REQUIRE(solver.getModel().heap());
    CHECK(solver.getModel().heap()->cells.empty());
    CHECK(solver.validateModel() == Solver::ModelValidation::Satisfied);
    auto notP = solver.mkConst(solver.boolSort(), "q");
    REQUIRE((solver.checkSatAssuming({notP}) == Result::Sat));
    REQUIRE(solver.getModel().heap());
    CHECK_FALSE(solver.getModel().heap()->cells.empty());
    solver.push();
    CHECK_FALSE(solver.getModel().heap());
    solver.assertFormula(p);
    REQUIRE((solver.checkSatAssuming({notP}) == Result::Unsat));
    CHECK_FALSE(solver.getModel().heap());
    CHECK_FALSE(solver.getUnsatCore().empty());
    CHECK(solver.getProof().isEmpty());
    solver.pop();
    REQUIRE((solver.checkSatAssuming({notP}) == Result::Sat));
    REQUIRE(solver.getModel().heap());
    CHECK_FALSE(solver.getModel().heap()->cells.empty());
    solver.reset();
    CHECK_FALSE(solver.getModel().heap());
}
