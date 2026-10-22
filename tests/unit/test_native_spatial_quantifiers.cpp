#include <doctest/doctest.h>
#include "decision/sl/NativeSeparation.h"
#include "decision/sl/NativeInductive.h"
#include <somtparser/frontend/parser.h>

using namespace xolver;
namespace {
struct QuantifiedCase { const char* formula; Result expected; };
const std::vector<QuantifiedCase> cases{
    {"(exists ((x Int)) (pto x (+ x 1)))", Result::Sat},
    {"(exists ((x Int)) (and (= x 3) (pto (ite sep.emp 2 x) (ite sep.emp 8 9))))", Result::Sat},
    {"(exists ((x Int)) (and (pto (ite sep.emp x 3) 9) (pto 4 9)))", Result::Unsat},
    {"(forall ((x Int)) (pto x 0))", Result::Unsat},
    {"(forall ((x Int)) (exists ((y Int)) (and (> y x) sep.emp)))", Result::Sat},
    {"(not (exists ((x Int)) (pto x 0)))", Result::Sat},
    {"(exists ((x Int)) (and (= x 17) (not (exists ((x Int)) (and (= x 18) (pto x 0)))) sep.emp))", Result::Sat},
    {"(and sep.emp (forall ((x Int)) (wand (pto x 0) (exists ((y Int)) (pto x y)))))", Result::Sat},
    {"(and sep.emp (wand (exists ((x Int)) (pto x 0)) (pto 1 0)))", Result::Unsat},
    {"(forall ((x Int)) (wand true sep.emp))", Result::Unsat},
    {"(forall ((b Bool)) (ite b sep.emp sep.emp))", Result::Sat},
    {"(exists ((x Int)) (sep (pto x 0) (pto x 1)))", Result::Unsat},
    {"(and (exists ((x Int)) (pto x 0)) (forall ((y Int)) (=> (= y 1) (not (pto y 0)))))", Result::Sat},
    {"(not (forall ((x Int)) (not (pto x 0))))", Result::Sat},
    {"(and sep.emp (not (forall ((x Int)) (not (pto x 0)))))", Result::Unsat},
};
}

TEST_CASE("native SL quantified search preserves binding polarity and extension witnesses") {
    for (const auto& entry : cases) {
        CAPTURE(std::string(entry.formula));
        SOMTParser::Parser parser;
        REQUIRE(parser.parseStr(std::string("(set-logic ALL)(declare-heap (Int Int))(assert ") + entry.formula + ")"));
        auto answer = sl::decideNative(parser.getHeapLocationSort(), parser.getHeapDataSort(),
            parser.getAssertions(), parser.getDeclaredVariables(), {3000000, 256});
        INFO(answer.reason);
        REQUIRE((answer.result == entry.expected));
        if (answer.result == Result::Sat) {
            REQUIRE(answer.model);
            CHECK(sl::checkInterpretation(*answer.model, {3000000, 256}).holds == std::optional<bool>(true));
            // Recompile the original quantified source on the exported concrete
            // heap. This does not rely on the searched heap-symbol assignment.
            for (const auto& root : parser.getAssertions())
                CHECK(sl::nativeValue(root, *answer.model, {3000000, 256}) == std::optional<std::string>("true"));
            for (const auto& [name, value] : answer.model->assignments)
                CHECK(name.find("@xolver.sl.heap.") != 0);
        }
    }
}

TEST_CASE("native SL finite heap search never treats its current size as an UNSAT theorem") {
    SOMTParser::Parser parser;
    // A concrete model consists of cells 1..100, all containing 0, with nil=0.
    // Failure to reach this size under a small work allowance is inconclusive.
    REQUIRE(parser.parseStr("(set-logic ALL)(declare-heap (Int Int))"
        "(assert (= (as sep.nil Int) 0))"
        "(assert (forall ((x Int)) (=> (and (<= 1 x) (<= x 100)) (sep (pto x 0) true))))"));
    auto answer = sl::decideNative(parser.getHeapLocationSort(), parser.getHeapDataSort(),
        parser.getAssertions(), parser.getDeclaredVariables(), {20000, 128});
    CHECK((answer.result != Result::Unsat));
    if (answer.result == Result::Unknown) {
        CHECK(answer.reason.find("limit") != std::string::npos);
        CHECK_FALSE(answer.model);
    } else {
        REQUIRE(answer.model);
        CHECK(answer.model->heap.cells.size() >= 100);
        CHECK(sl::checkInterpretation(*answer.model, {3000000, 256}).holds == std::optional<bool>(true));
    }
}

TEST_CASE("native SL spatial quantifiers obey zero work budgets") {
    SOMTParser::Parser parser;
    REQUIRE(parser.parseStr("(set-logic ALL)(declare-heap (Int Int))(assert (exists ((x Int)) (pto x 0)))"));
    auto answer = sl::decideNative(parser.getHeapLocationSort(), parser.getHeapDataSort(),
        parser.getAssertions(), parser.getDeclaredVariables(), {0, 128});
    CHECK((answer.result == Result::Unknown));
    CHECK_FALSE(answer.model);
}

TEST_CASE("native SL diagnoses unsupported heap domains before search retries") {
    for (const auto& input : {
        "(declare-heap (Bool Int))(assert (exists ((x Bool)) (pto x 0)))",
        "(declare-heap (Int Bool))(assert (exists ((x Int)) (pto x true)))",
        "(declare-sort L 0)(declare-heap (L Int))(assert (exists ((x L)) (pto x 0)))"}) {
        CAPTURE(std::string(input));
        SOMTParser::Parser parser;
        REQUIRE(parser.parseStr(std::string("(set-logic ALL)") + input));
        for (uint64_t budget : {64, 4096}) {
            const sl::Limits limits{budget, 128};
            auto ordinary = sl::decideNative(parser.getHeapLocationSort(), parser.getHeapDataSort(),
                parser.getAssertions(), parser.getDeclaredVariables(), limits);
            auto inductive = sl::decideInductiveNative(parser.getHeapLocationSort(), parser.getHeapDataSort(),
                parser.getAssertions(), parser.getDeclaredVariables(), {}, limits);
            for (const auto& answer : {ordinary, inductive}) {
                CHECK((answer.result == Result::Unknown));
                CHECK(answer.reason == "SL native heap domain currently requires (Int Int)");
                CHECK(answer.work == 0);
                CHECK_FALSE(answer.model);
            }
        }
    }
}

TEST_CASE("native SL exact heap anchors preserve free values and all residual conjuncts") {
    for (const auto& [query, result] : std::vector<std::pair<std::string, Result>>{
        {"(and (sep (pto a b) (pto b c)) (exists ((z Int)) (sep (pto a z) (pto z c))))", Result::Sat},
        {"(and (sep (and (pto a b) (= a b)) (pto b c)) (exists ((z Int)) (pto z c)))", Result::Unsat},
        {"(and (sep (pto a b) (pto b c)) (forall ((z Int)) (=> (= z a) (sep (pto z b) (pto b c)))))", Result::Sat},
    }) {
        CAPTURE(query);
        SOMTParser::Parser parser;
        REQUIRE(parser.parseStr("(set-logic ALL)(declare-heap (Int Int))"
            "(declare-const a Int)(declare-const b Int)(declare-const c Int)(assert " + query + ")"));
        auto answer = sl::decideNative(parser.getHeapLocationSort(), parser.getHeapDataSort(),
            parser.getAssertions(), parser.getDeclaredVariables(), {3000000, 256});
        INFO(answer.reason);
        REQUIRE((answer.result == result));
        if (answer.result == Result::Sat) {
            REQUIRE(answer.model);
            CHECK(answer.model->heap.cells.size() == 2);
            CHECK(sl::nativeValue(parser.getAssertions().at(0), *answer.model, {3000000, 256}) == std::optional<std::string>("true"));
        }
    }
}
