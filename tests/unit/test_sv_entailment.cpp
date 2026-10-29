#include "applications/verification/sl/Entailment.h"
#include "ir/NativeBuilder.h"
#include <doctest/doctest.h>
#include <somtparser/frontend/parser.h>
#include <tuple>

using namespace xolver;
namespace {
struct Query {
    SOMTParser::Parser parser;
    sl::EntailmentProblem problem;
    Query(const std::string &definitions, const std::string &antecedent,
          const std::string &conclusion) {
        if (!parser.parseStr("(set-logic ALL)(declare-heap (Int Int))(declare-const n "
                             "Int)(declare-const x Int)(declare-const y Int)" +
                             definitions + "(assert " + antecedent + ")"))
            throw std::runtime_error("SV entailment test parse failed");
        problem.context.location = parser.getHeapLocationSort();
        problem.context.data = parser.getHeapDataSort();
        problem.context.assertions = parser.getAssertions();
        problem.context.declarations = parser.getDeclaredVariables();
        problem.context.recursion = sl::RecursiveSemantics::LeastFixedPoint;
        for (const auto &item : parser.getRecursiveDefinitions())
            problem.context.definitions.push_back(
                {item.symbol, item.definition->getFuncBody(), item.definition->getFuncParams()});
        problem.conclusion = parser.mkExpr(conclusion);
    }
};
const std::string countdown = "(define-fun-rec p ((n Int)) Bool (or (and (= n 0) sep.emp) (and (> "
                              "n 0) (sep (pto n (- n 1)) (p (- n 1))))))";
} // namespace
TEST_CASE("SV SL: entailments preserve shared heaps and countermodels") {
    for (const auto &[left, right, valid] : std::vector<std::tuple<std::string, std::string, bool>>{
             {"(pto x y)", "(distinct x (as sep.nil Int))", true},
             {"(pto x y)", "sep.emp", false},
             {"(sep (pto x 1) (pto y 2))", "(distinct x y)", true},
             {"(and sep.emp (= x y))", "(wand (pto x 1) (pto y 1))", true}}) {
        INFO(left);
        INFO(right);
        Query query("", left, right);
        auto answer = sl::EntailmentSolver().solve(query.problem);
        INFO(answer.reason);
        REQUIRE(answer.status ==
                (valid ? sl::EntailmentStatus::Valid : sl::EntailmentStatus::Invalid));
        if (valid) {
            REQUIRE(answer.certificate);
            CHECK(sl::EntailmentCertificateSolver()
                      .solve({query.problem, *answer.certificate})
                      .status == sl::EntailmentStatus::Valid);
        } else {
            REQUIRE(answer.counterexample);
            CHECK(sl::checkInterpretation(*answer.counterexample).holds ==
                  std::optional<bool>(true));
        }
    }
}
TEST_CASE("SV SL: recursive arithmetic invariants prove unbounded entailments") {
    Query query(countdown, "(p n)", "(>= n 0)");
    auto &definition = query.problem.context.definitions[0];
    native::Nodes b({definition.body});
    auto zero = b.make(SOMTParser::SortManager::getInt(), native::K::NT_CONST, {}, "0");
    auto invariant = b.logical(native::K::NT_GE, {definition.parameters[0], zero});
    query.problem.context.invariantCandidates = {{definition.symbol, invariant}};
    auto answer = sl::EntailmentSolver({3000000, 256}).solve(query.problem);
    INFO(answer.reason);
    REQUIRE(answer.status == sl::EntailmentStatus::Valid);
    REQUIRE(answer.certificate);
    REQUIRE(answer.certificate->invariants.size() == 1);
    CHECK(answer.certificate->unfoldingDepth == std::optional<std::size_t>(0));
    CHECK(answer.inference.complete);
    CHECK(sl::EntailmentCertificateSolver({3000000, 256})
              .solve({query.problem, *answer.certificate})
              .status == sl::EntailmentStatus::Valid);
    auto forged = *answer.certificate;
    forged.invariants[0].property = b.logical(native::K::NT_GT, {definition.parameters[0], zero});
    CHECK(sl::EntailmentCertificateSolver({3000000, 256}).solve({query.problem, forged}).status ==
          sl::EntailmentStatus::Invalid);
    auto request = query.problem.context;
    request.assertions.push_back(b.negate(query.problem.conclusion));
    CHECK((sl::Solver({3000000, 256}).solve(request).result == Result::Unsat));
}
TEST_CASE("SV SL: least fixed point emptiness is proved rather than assumed") {
    Query query("(define-fun-rec p ((n Int)) Bool (p n))", "(p 1)", "false");
    auto answer = sl::EntailmentSolver({200000, 256}).solve(query.problem);
    INFO(answer.reason);
    REQUIRE(answer.status == sl::EntailmentStatus::Valid);
    REQUIRE(answer.certificate);
    REQUIRE(answer.certificate->invariants.size() == 1);
    CHECK(sl::EntailmentCertificateSolver({200000, 256})
              .solve({query.problem, *answer.certificate})
              .status == sl::EntailmentStatus::Valid);
    Query nonempty("(define-fun-rec p ((n Int)) Bool (or sep.emp (p n)))", "(p 1)", "false");
    auto invalid = sl::EntailmentSolver({200000, 256}).solve(nonempty.problem);
    REQUIRE(invalid.status == sl::EntailmentStatus::Invalid);
    REQUIRE(invalid.counterexample);
    CHECK(invalid.counterexample->heap.cells.empty());
}
TEST_CASE("SV SL: spatial inductive summaries and dependent candidate removal") {
    Query query(
        "(define-fun-rec p ((n Int)) Bool (or (and (= n 0) sep.emp) (and (> n 0) (p (- n 1)))))",
        "(p n)", "sep.emp");
    auto &definition = query.problem.context.definitions[0];
    query.problem.context.invariantCandidates = {{definition.symbol, query.problem.conclusion}};
    auto answer = sl::EntailmentSolver({3000000, 256}).solve(query.problem);
    INFO(answer.reason);
    REQUIRE(answer.status == sl::EntailmentStatus::Valid);
    REQUIRE(answer.certificate);
    CHECK(sl::EntailmentCertificateSolver({3000000, 256})
              .solve({query.problem, *answer.certificate})
              .status == sl::EntailmentStatus::Valid);
    native::Nodes b({});
    auto broken = *answer.certificate;
    broken.invariants = {{definition.symbol, b.boolean(true)}};
    broken.unfoldingDepth = 0;
    CHECK(sl::EntailmentCertificateSolver({3000000, 256}).solve({query.problem, broken}).status ==
          sl::EntailmentStatus::Invalid);
    Query dependency(
        "(define-fun-rec q ((n Int)) Bool sep.emp)(define-fun-rec p ((n Int)) Bool (q n))", "true",
        "true");
    for (const auto &def : dependency.problem.context.definitions)
        dependency.problem.context.invariantCandidates.push_back({def.symbol, b.boolean(false)});
    auto inference = sl::InductiveInvariantSolver().solve(dependency.problem.context);
    REQUIRE(inference.complete);
    CHECK(inference.invariants.empty());
    CHECK(inference.refuted.size() == 2);
}
TEST_CASE("SV SL: invalid semantics and exhausted proof search preserve unknown") {
    Query query(countdown, "(p n)", "(>= n 0)");
    CHECK(sl::EntailmentSolver({1, 256}).solve(query.problem).status ==
          sl::EntailmentStatus::Unknown);
    query.problem.context.recursion = sl::RecursiveSemantics::Equations;
    CHECK(sl::EntailmentSolver().solve(query.problem).status == sl::EntailmentStatus::Unknown);
    Query bad("(define-fun-rec p ((n Int)) Bool (not (p n)))", "true", "true");
    CHECK(sl::EntailmentSolver().solve(bad.problem).status == sl::EntailmentStatus::Unknown);
    query.problem.conclusion = {};
    CHECK(sl::EntailmentSolver().solve(query.problem).status == sl::EntailmentStatus::InvalidInput);
}
