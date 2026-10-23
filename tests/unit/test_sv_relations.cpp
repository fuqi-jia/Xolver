#include "applications/sv/sl/Entailment.h"
#include "ir/NativeBuilder.h"
#include <doctest/doctest.h>
#include <somtparser/frontend/parser.h>

using namespace xolver;
namespace {
struct Query {
    SOMTParser::Parser parser;
    sl::EntailmentProblem problem;
    Query(const std::string &definitions, const std::string &antecedent,
          const std::string &conclusion) {
        if (!parser.parseStr("(set-logic ALL)(declare-heap (Int Int))(declare-const n Int)"
                             "(declare-const x Int)(declare-const y Int)" +
                             definitions + "(assert " + antecedent + ")"))
            throw std::runtime_error("SL relation test parsing failed");
        auto &c = problem.context;
        c.location = parser.getHeapLocationSort();
        c.data = parser.getHeapDataSort();
        c.assertions = parser.getAssertions();
        c.declarations = parser.getDeclaredVariables();
        c.recursion = sl::RecursiveSemantics::LeastFixedPoint;
        for (const auto &d : parser.getRecursiveDefinitions())
            c.definitions.push_back(
                {d.symbol, d.definition->getFuncBody(), d.definition->getFuncParams()});
        problem.conclusion = parser.mkExpr(conclusion);
    }
    const sl::InductiveDefinition &definition(const std::string &name) {
        for (const auto &d : problem.context.definitions)
            if (d.symbol->getName() == name)
                return d;
        throw std::runtime_error("missing test predicate");
    }
    native::Node call(const std::string &name, std::vector<native::Node> arguments) {
        native::Nodes b({});
        auto symbol = definition(name).symbol;
        arguments.insert(arguments.begin(), symbol);
        return b.make(SOMTParser::SortManager::getBool(), native::K::NT_FUNC_REC_APPLY,
                      std::move(arguments), name);
    }
};
const std::string countdown = "(define-fun-rec p ((n Int)) Bool (or (and (= n 0) sep.emp) "
                              "(and (> n 0) (sep (pto n (- n 1)) (p (- n 1))))))"
                              "(define-fun-rec q ((n Int)) Bool (or (and (<= n 0) sep.emp) "
                              "(and (>= n 1) (sep (q (- n 1)) (pto n (- n 1))))))";
void valid(Query &query) {
    auto answer = sl::EntailmentSolver({3000000, 256}).solve(query.problem);
    INFO(answer.reason);
    REQUIRE(answer.status == sl::EntailmentStatus::Valid);
    REQUIRE(answer.certificate);
    CHECK(answer.certificate->method == sl::EntailmentProof::StructuralInduction);
    CHECK(sl::EntailmentCertificateSolver({3000000, 256})
              .solve({query.problem, *answer.certificate})
              .status == sl::EntailmentStatus::Valid);
    auto forged = *answer.certificate;
    native::Nodes b({});
    forged.relations.push_back({query.definition("p").symbol, b.boolean(false)});
    CHECK(sl::EntailmentCertificateSolver({3000000, 256}).solve({query.problem, forged}).status ==
          sl::EntailmentStatus::Invalid);
    CHECK(sl::EntailmentCertificateSolver({1, 256})
              .solve({query.problem, *answer.certificate})
              .status == sl::EntailmentStatus::Unknown);
    auto altered = query.problem;
    for (auto &definition : altered.context.definitions)
        if (definition.symbol == query.definition("q").symbol)
            definition.body = b.boolean(false);
    CHECK(sl::EntailmentCertificateSolver({3000000, 256})
              .solve({altered, *answer.certificate})
              .status == sl::EntailmentStatus::Invalid);
}
} // namespace
TEST_CASE("SV SL relations: unbounded predicate inclusion and exact separating frames") {
    Query query(countdown, "(p n)", "(q n)");
    valid(query);
    Query framed(countdown, "(sep (pto 100 9) (p n))", "(sep (q n) (pto 100 9))");
    valid(framed);
    Query dropped(countdown, "(sep (pto 100 9) (p 0))", "(q 0)");
    auto answer = sl::EntailmentSolver({3000000, 256}).solve(dropped.problem);
    INFO(answer.reason);
    REQUIRE(answer.status == sl::EntailmentStatus::Invalid);
    REQUIRE(answer.counterexample);
    CHECK(answer.counterexample->heap.cells.size() == 1);
    for (int n : {3, 4}) {
        auto value = std::to_string(n);
        Query larger(countdown, "(sep (pto 100 9) (p " + value + "))", "(q " + value + ")");
        auto counter = sl::EntailmentSolver({3000000, 256}).solve(larger.problem);
        INFO(counter.reason);
        REQUIRE(counter.status == sl::EntailmentStatus::Invalid);
        REQUIRE(counter.counterexample);
        CHECK(counter.counterexample->heap.cells.size() == std::size_t(n + 1));
        CHECK(sl::checkInterpretation(*counter.counterexample).holds == std::optional<bool>(true));
    }
}
TEST_CASE("SV SL relations: reversal and negative occurrences do not inherit a forward lemma") {
    for (const auto &[a, b] : std::vector<std::pair<std::string, std::string>>{
             {"(q (- 1))", "(p (- 1))"}, {"(not (p (- 1)))", "(not (q (- 1)))"}}) {
        Query query(countdown, a, b);
        auto answer = sl::EntailmentSolver({3000000, 256}).solve(query.problem);
        INFO(answer.reason);
        REQUIRE(answer.status == sl::EntailmentStatus::Invalid);
        REQUIRE(answer.counterexample);
        CHECK(answer.counterexample->heap.cells.empty());
    }
}
TEST_CASE("SV SL relations: conditional induction closes guarded reversals and contraposition") {
    Query guarded(countdown, "(and (q n) (>= n 0))", "(p n)");
    valid(guarded);
    Query ground(countdown, "(q 3)", "(p 3)");
    valid(ground);
    Query negative(countdown, "(not (p 3))", "(not (q 3))");
    valid(negative);
}
TEST_CASE("SV SL relations: quantified lists and explicit parameter permutations") {
    const std::string definitions =
        "(define-fun-rec p ((a Int) (b Int)) Bool (or (and (= a b) sep.emp) "
        "(exists ((z Int)) (sep (pto a z) (p z b)))))"
        "(define-fun-rec q ((end Int) (start Int)) Bool (or (and (= start end) sep.emp) "
        "(exists ((w Int)) (sep (q end w) (pto start w)))))";
    Query query(definitions, "(p x y)", "(q y x)");
    auto params = query.definition("p").parameters;
    query.problem.lemmaCandidates = {
        {query.definition("p").symbol, query.call("q", {params[1], params[0]})}};
    valid(query);
    Query direct("(define-fun-rec p ((a Int) (b Int)) Bool (or (and (= a b) sep.emp) (exists ((z "
                 "Int)) (sep (pto a z) (p z b)))))"
                 "(define-fun-rec q ((a Int) (b Int)) Bool (or (and (= a b) sep.emp) (exists ((w "
                 "Int)) (sep (q w b) (pto a w)))))",
                 "(p x y)", "(q x y)");
    valid(direct);
}
TEST_CASE("SV SL relations: mutually recursive hypotheses are rechecked after removal") {
    Query query(
        "(define-funs-rec ((p ((n Int)) Bool) (r ((n Int)) Bool) (q ((n Int)) Bool) (s ((n Int)) "
        "Bool)) "
        "((or (and (= n 0) sep.emp) (and (> n 0) (sep (pto n (- n 1)) (r (- n 1))))) "
        "(p n) (or (and (<= n 0) sep.emp) (and (> n 0) (sep (s (- n 1)) (pto n (- n 1))))) (q n)))",
        "(p n)", "(q n)");
    valid(query);
    Query bad("(define-fun-rec p ((n Int)) Bool sep.emp)(define-fun-rec q ((n Int)) Bool (p n))",
              "false", "true");
    native::Nodes b({});
    sl::RelationProblem problem{bad.problem.context,
                                {{bad.definition("p").symbol, b.boolean(false)},
                                 {bad.definition("q").symbol, b.boolean(false)}}};
    auto inferred = sl::RelationSolver({3000000, 256}).solve(problem);
    INFO(inferred.reason);
    REQUIRE(inferred.complete);
    CHECK(inferred.relations.empty());
    CHECK(inferred.unproved.size() == 2);
}
TEST_CASE("SV SL relations: a recursive consequent cannot close its own proof") {
    Query query("(define-fun-rec p ((n Int)) Bool sep.emp)(define-fun-rec q ((n Int)) Bool (q n))",
                "(p 1)", "(q 1)");
    auto params = query.definition("p").parameters;
    auto falseLemma = sl::PredicateRelation{query.definition("p").symbol, query.call("q", params)};
    auto inferred = sl::RelationSolver().solve({query.problem.context, {falseLemma}});
    REQUIRE(inferred.complete);
    CHECK(inferred.relations.empty());
    auto answer = sl::EntailmentSolver({3000000, 256}).solve(query.problem);
    INFO(answer.reason);
    REQUIRE(answer.status == sl::EntailmentStatus::Invalid);
    REQUIRE(answer.counterexample);
    CHECK(answer.counterexample->heap.cells.empty());
    query.problem.conclusion = query.parser.mkExpr("true");
    sl::EntailmentCertificate forged;
    forged.method = sl::EntailmentProof::StructuralInduction;
    forged.relations = {falseLemma};
    CHECK(sl::EntailmentCertificateSolver().solve({query.problem, forged}).status ==
          sl::EntailmentStatus::Invalid);
}
TEST_CASE("SV SL expansion: free symbols keep identity and emp is the star identity") {
    Query query("(declare-const g Int)(define-fun-rec p ((n Int)) Bool (or (and (= n 0) (>= g 0) "
                "sep.emp) (and (> n 0) (sep (pto n g) (p (- n 1))))))",
                "(p 2)", "(>= g 0)");
    auto &context = query.problem.context;
    context.invariantCandidates = {{query.definition("p").symbol, query.parser.mkExpr("(>= g 0)")}};
    auto answer = sl::EntailmentSolver({3000000, 256}).solve(query.problem);
    INFO(answer.reason);
    REQUIRE(answer.status == sl::EntailmentStatus::Valid);
    CHECK(sl::EntailmentCertificateSolver().solve({query.problem, *answer.certificate}).status ==
          sl::EntailmentStatus::Valid);
    Query empty("(define-fun-rec p ((n Int)) Bool (sep sep.emp sep.emp))", "(p 1)", "sep.emp");
    answer = sl::EntailmentSolver().solve(empty.problem);
    INFO(answer.reason);
    CHECK(answer.status == sl::EntailmentStatus::Valid);
}
