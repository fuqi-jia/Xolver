#include <doctest/doctest.h>
#include "applications/sv/sl/NativeInductive.h"
#include <somtparser/frontend/parser.h>

using namespace xolver;
namespace {
sl::NativeDecision inductive(const std::string& definitions, const std::string& query, uint64_t steps = 3000000) {
    SOMTParser::Parser parser;
    if (!parser.parseStr("(set-logic ALL)(declare-heap (Int Int))" + definitions + "(assert " + query + ")"))
        throw std::runtime_error("inductive SL test failed to parse");
    std::vector<sl::InductiveDefinition> environment;
    for (const auto& item : parser.getRecursiveDefinitions())
        environment.push_back({item.symbol, item.definition->getFuncBody(), item.definition->getFuncParams()});
    // The library caller explicitly chooses SL inductive semantics. Merely
    // parsing define-fun-rec under ALL does not select LFP in the CLI.
    return sl::decideInductiveNative(parser.getHeapLocationSort(), parser.getHeapDataSort(),
        parser.getAssertions(), parser.getDeclaredVariables(), environment, {steps, 256});
}
const std::string list =
    "(define-fun-rec ls ((x Int) (y Int)) Bool "
    "(or (and (= x y) sep.emp) "
    "(exists ((z Int)) (and (distinct x y) (sep (pto x z) (ls z y))))))";
}

TEST_CASE("native SL inductive unfoldings preserve recursive heap ownership and alpha binding") {
    for (const auto& [query, expected] : std::vector<std::pair<std::string, Result>>{
        {"(ls 1 1)", Result::Sat},
        {"(and (ls 1 2) (pto 1 2))", Result::Sat},
        {"(and (ls 1 3) (sep (pto 1 2) (pto 2 3)))", Result::Sat},
        {"(sep (ls 1 2) (pto 1 2))", Result::Unsat},
        {"(and sep.emp (not (ls 1 1)))", Result::Unsat},
        {"(and sep.emp (not (ls 1 2)))", Result::Sat},
    }) {
        CAPTURE(query);
        auto result = inductive(list, query);
        INFO(result.reason);
        REQUIRE((result.result == expected));
        if (result.result == Result::Sat) {
            REQUIRE(result.model);
            CHECK(sl::checkInterpretation(*result.model, {3000000, 256}).holds == std::optional<bool>(true));
        }
    }
}

TEST_CASE("native SL rejects nonpositive definitions even when their calls are unused") {
    auto result = inductive("(define-fun-rec p () Bool (not p))", "true");
    CHECK((result.result == Result::Unknown));
    CHECK(result.reason.find("positive") != std::string::npos);
    CHECK_FALSE(result.model);
    auto antecedent = inductive("(define-fun-rec p () Bool (wand p false))", "sep.emp");
    CHECK((antecedent.result == Result::Unknown));
    CHECK(antecedent.reason.find("positive") != std::string::npos);
}

TEST_CASE("native SL inductive depth exhaustion does not turn an upper model into SAT") {
    auto result = inductive("(define-fun-rec p ((x Int)) Bool (p x))", "(p 1)", 20000);
    CHECK((result.result == Result::Unknown));
    CHECK(result.reason.find("limit") != std::string::npos);
    CHECK_FALSE(result.model);
}

TEST_CASE("native SL recursive countdown can grow beyond the first unfolding") {
    const std::string definition = "(define-fun-rec p ((x Int)) Bool "
        "(or (and (= x 0) sep.emp) (and (> x 0) (sep (pto x (- x 1)) (p (- x 1))))))";
    auto result = inductive(definition, "(and (p 2) (sep (pto 2 1) (pto 1 0)))");
    INFO(result.reason);
    REQUIRE((result.result == Result::Sat));
    REQUIRE(result.model);
    CHECK(result.model->heap.cells.size() == 2);
    CHECK(sl::checkInterpretation(*result.model, {3000000, 256}).holds == std::optional<bool>(true));
}

TEST_CASE("native SL heap dependent actuals retain their value at the calling heap") {
    // SL-COMP first-order actuals are heap independent. This tests the explicit
    // API extension that also accepts spatial Bool and spatial-ite Int actuals.
    const std::string boolean = "(define-fun-rec p ((b Bool)) Bool (sep b (pto 1 0)))";
    const std::string integer = "(define-fun-rec p ((x Int)) Bool (sep (= x 2) (pto 1 0)))";
    const std::string wand = "(define-fun-rec p ((b Bool)) Bool (wand (pto 1 0) b))";
    struct Entry { std::string definition, query, witness; Result expected; };
    for (const auto& entry : std::vector<Entry>{
        {boolean, "(p sep.emp)", "", Result::Unsat},
        {boolean, "(and (pto 1 0) (p (not sep.emp)))", "(pto 1 0)", Result::Sat},
        {boolean, "(and (pto 1 0) (not (p sep.emp)))", "(pto 1 0)", Result::Sat},
        {integer, "(p (ite sep.emp 2 3))", "", Result::Unsat},
        {integer, "(and (pto 1 0) (p (ite sep.emp 3 2)))", "(pto 1 0)", Result::Sat},
        {wand, "(and sep.emp (p sep.emp))", "sep.emp", Result::Sat},
        {wand, "(and sep.emp (not (p sep.emp)))", "", Result::Unsat},
    }) {
        CAPTURE(entry.query);
        auto result = inductive(entry.definition, "(and (= (as sep.nil Int) 0) " + entry.query + ")");
        INFO(result.reason);
        REQUIRE((result.result == entry.expected));
        if (result.result == Result::Sat) {
            REQUIRE(result.model);
            CHECK(sl::checkInterpretation(*result.model, {3000000, 256}).holds == std::optional<bool>(true));
            SOMTParser::Parser expected;
            REQUIRE(expected.parseStr("(set-logic ALL)(declare-heap (Int Int))(assert " + entry.witness + ")"));
            CHECK(sl::nativeValue(expected.getAssertions().at(0), *result.model, {3000000, 256}) == std::optional<std::string>("true"));
            CHECK(result.model->heap.nil == "0");
        }
    }
}
