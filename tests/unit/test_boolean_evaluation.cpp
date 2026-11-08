#include "ir/PartialBooleanEvaluation.h"
#include "evidence/ModelValidator.h"
#include "search/boolean/BooleanDefinitions.h"
#include <doctest/doctest.h>
#include <array>
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
class BooleanClauseCollector final : public SatSolver {
public:
    SatVar variables = 0;
    std::vector<std::vector<SatLit>> clauses;
    SatVar newVar() override { return ++variables; }
    void addClause(const std::vector<SatLit>& clause) override { clauses.push_back(clause); }
    SolveResult solve() override { return SolveResult::Unknown; }
    SolveResult solve(const std::vector<SatLit>&) override { return SolveResult::Unknown; }
    bool value(SatVar) const override { return false; }
    void setDeadline(std::chrono::steady_clock::time_point) override {}

    // Exhaustive tests compare clause propagation against the independently
    // enumerated Boolean relation, without a SAT search hiding missed units.
    bool propagate(std::vector<int>& values) const {
        bool changed;
        do {
            changed = false;
            for (const auto& clause : clauses) {
                bool satisfied = false;
                unsigned unassigned = 0;
                SatLit remaining;
                for (const auto literal : clause) {
                    if (values[literal.var] < 0) {
                        ++unassigned;
                        remaining = literal;
                    } else if (values[literal.var] == int(literal.sign)) {
                        satisfied = true;
                        break;
                    }
                }
                if (satisfied) continue;
                if (unassigned == 0) return false;
                if (unassigned == 1) {
                    values[remaining.var] = int(remaining.sign);
                    changed = true;
                }
            }
        } while (changed);
        return true;
    }
};
}

TEST_CASE("Boolean definitions: ordered ITE propagates its full relation") {
    for (unsigned polarity = 0; polarity < 16; ++polarity) {
        BooleanClauseCollector sat;
        std::array<SatLit, 4> literals;
        for (unsigned i = 0; i < literals.size(); ++i)
            literals[i] = SatLit(sat.newVar(), bool(polarity & (1u << i)));
        emitBooleanOrderedIteDefinition(sat, literals[3], literals[0], literals[1], literals[2]);
        std::vector<unsigned> models;
        for (unsigned mask = 0; mask < 16; ++mask) {
            const auto value = [&](unsigned i) {
                return bool(mask & (1u << i)) == literals[i].sign;
            };
            const bool expected = (!value(1) || value(2)) &&
                                  value(3) == (value(0) ? value(1) : value(2));
            bool clausesHold = true;
            for (const auto& clause : sat.clauses) {
                bool holds = false;
                for (const auto literal : clause)
                    holds |= bool(mask & (1u << (literal.var - 1))) == literal.sign;
                clausesHold &= holds;
            }
            CHECK(clausesHold == expected);
            if (expected) models.push_back(mask);
        }
        for (unsigned partial = 0; partial < 81; ++partial) {
            std::vector<int> initial(5, -1);
            auto digits = partial;
            for (unsigned i = 1; i <= 4; ++i, digits /= 3)
                initial[i] = int(digits % 3) - 1;
            std::vector<unsigned> compatible;
            for (const auto mask : models) {
                bool matches = true;
                for (unsigned i = 1; i <= 4; ++i)
                    matches &= initial[i] < 0 || initial[i] == int(bool(mask & (1u << (i - 1))));
                if (matches) compatible.push_back(mask);
            }
            auto closure = initial;
            CHECK(sat.propagate(closure) == !compatible.empty());
            if (compatible.empty()) continue;
            for (unsigned i = 1; i <= 4; ++i) {
                const int first = bool(compatible.front() & (1u << (i - 1)));
                bool forced = true;
                for (const auto mask : compatible)
                    forced &= int(bool(mask & (1u << (i - 1)))) == first;
                if (forced) CHECK(closure[i] == first);
            }
        }
    }
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

TEST_CASE("Boolean definitions: shared occurrences and nary implications preserve every polarity") {
    BooleanFixture f;
    const auto a = f.variable("a"), b = f.variable("b"), c = f.variable("c");
    const auto left = f.node(Kind::And, {a, b});
    const auto middle = f.node(Kind::Or, {b, c});
    const auto right = f.node(Kind::And, {a, c});
    const auto implication = f.node(Kind::Implies, {left, middle, right});
    const std::vector roots{implication, f.node(Kind::Not, {right})};
    auto polarities = computeBooleanPolarities(roots, f.terms);
    CHECK(polarities.at(left) == 2);
    CHECK(polarities.at(middle) == 2);
    CHECK(polarities.at(right) == 3);
    CHECK_FALSE(booleanDefinitionDirections(polarities, left).positive);
    CHECK(booleanDefinitionDirections(polarities, left).negative);
    CHECK(booleanDefinitionDirections(polarities, NullExpr).positive);
    CHECK(booleanDefinitionDirections(polarities, NullExpr).negative);
    const std::vector nonmonotone{f.node(Kind::Xor, {left, middle, right})};
    polarities = computeBooleanPolarities(nonmonotone, f.terms);
    for (const auto child : {left, middle, right}) CHECK(polarities.at(child) == 3);
    auto deep = a;
    for (unsigned i = 0; i < 30001; ++i) deep = f.node(Kind::Not, {deep});
    const std::vector deepRoots{deep};
    polarities = computeBooleanPolarities(deepRoots, f.terms);
    CHECK(polarities.at(a) == 2);
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
