#include "ir/PartialBooleanEvaluation.h"
#include "evidence/ModelValidator.h"
#include <doctest/doctest.h>
#include <utility>
#include <vector>

using namespace xolver;

namespace {
struct BooleanFixture {
    NativeTerms terms;
    BooleanFixture() {
        terms.registerSort(0, SortKind::Bool);
        terms.registerSort(1, SortKind::Int);
        terms.setBoolSortId(0);
        terms.setIntSortId(1);
    }
    ExprId variable(const char* name) {
        return terms.add({Kind::Variable, 0, {}, Payload(std::string(name))});
    }
    ExprId constant(bool value) { return terms.add({Kind::ConstBool, 0, {}, Payload(value)}); }
    ExprId node(Kind kind, std::vector<ExprId> children) {
        TermExpr result{kind, 0, {}, {}};
        for (auto child : children) result.children.push_back(child);
        return terms.add(std::move(result));
    }
};
}

TEST_CASE("PartialBooleanEvaluation: nary connectives agree with exact truth tables") {
    BooleanFixture f;
    const auto a = f.variable("a"), b = f.variable("b"), c = f.variable("c");
    const auto implication = f.node(Kind::Implies, {a, b, c});
    const auto parity = f.node(Kind::Xor, {a, b, c});
    const auto equality = f.node(Kind::Eq, {a, b, c});
    const auto distinct = f.node(Kind::Distinct, {a, b, c});
    for (unsigned mask = 0; mask < 8; ++mask) {
        const bool av = mask & 1, bv = mask & 2, cv = mask & 4;
        const ModelValidator::BoolAssignment assignment{{a, av}, {b, bv}, {c, cv}};
        PartialBooleanEvaluation evaluation(f.terms, [&](ExprId id) -> std::optional<bool> {
            const auto found = assignment.find(id);
            return found == assignment.end() ? std::nullopt : std::optional<bool>(found->second);
        });
        ModelValidator validator;
        for (const auto& [root, expected] : std::vector<std::pair<ExprId, bool>>{
                 {implication, !av || !bv || cv}, {parity, (av != bv) != cv},
                 {equality, av == bv && bv == cv}, {distinct, false}}) {
            CHECK(evaluation.evaluate(root) == std::optional<bool>(expected));
            CHECK(validator.eval(root, f.terms, assignment) == expected);
        }
    }
}

TEST_CASE("PartialBooleanEvaluation: unknown atoms preserve polarity and conditional semantics") {
    BooleanFixture f;
    const auto atom = f.variable("unknown"), yes = f.constant(true), no = f.constant(false);
    const auto integer = f.terms.add({Kind::ConstInt, 1, {}, Payload(std::string("0"))});
    const auto arithmetic = f.node(Kind::Eq, {integer, integer});
    PartialBooleanEvaluation evaluation(f.terms, {});
    CHECK_FALSE(evaluation.evaluate(atom).has_value());
    CHECK_FALSE(evaluation.evaluate(f.node(Kind::Not, {atom})).has_value());
    CHECK_FALSE(evaluation.evaluate(arithmetic).has_value());
    CHECK_FALSE(evaluation.evaluate(f.node(Kind::Not, {arithmetic})).has_value());
    CHECK_FALSE(evaluation.evaluate(f.node(Kind::Xor, {})).has_value());
    CHECK_FALSE(evaluation.evaluate(f.node(Kind::Xor, {yes})).has_value());
    CHECK(evaluation.evaluate(f.node(Kind::And, {atom, no})) == false);
    CHECK(evaluation.evaluate(f.node(Kind::Or, {atom, yes})) == true);
    CHECK(evaluation.evaluate(f.node(Kind::Ite, {atom, yes, yes})) == true);
    CHECK_FALSE(evaluation.evaluate(f.node(Kind::Ite, {atom, yes, no})).has_value());
    CHECK(evaluation.evaluate(f.node(Kind::Implies, {atom, no, atom})) == true);
}

TEST_CASE("PartialBooleanEvaluation: deep shared DAGs use one stable atom snapshot") {
    BooleanFixture f;
    const auto atom = f.variable("a");
    auto deep = atom;
    for (int depth = 0; depth < 30000; ++depth) deep = f.node(Kind::Not, {deep});
    const auto root = f.node(Kind::And, {deep, deep, deep});
    unsigned calls = 0;
    PartialBooleanEvaluation evaluation(f.terms, [&](ExprId id) -> std::optional<bool> {
        if (id != atom) return std::nullopt;
        ++calls;
        return true;
    });
    CHECK(evaluation.evaluate(root) == true);
    CHECK(evaluation.evaluate(deep) == true);
    CHECK(calls == 1);
    PartialBooleanEvaluation replaced(f.terms, [&](ExprId id) -> std::optional<bool> {
        return id == atom ? std::optional<bool>(false) : std::nullopt;
    });
    CHECK(replaced.evaluate(root) == false);
    CHECK(evaluation.evaluate(root) == true);
}
