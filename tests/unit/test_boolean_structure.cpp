#include <doctest/doctest.h>
#include "search/boolean/BooleanStructure.h"

using namespace xolver;

namespace {
struct BooleanStructureFixture {
    NativeTerms terms;
    BooleanStructureFixture() {
        terms.registerSort(0, SortKind::Bool);
        terms.registerSort(1, SortKind::Real);
        terms.setBoolSortId(0);
        terms.setRealSortId(1);
    }
    ExprId variable(const char* name, SortId sort = 0) {
        return terms.add({Kind::Variable, sort, {}, Payload(std::string(name))});
    }
    ExprId node(Kind kind, std::initializer_list<ExprId> children) {
        return terms.add({kind, 0, children, {}});
    }
    bool alternatives(ExprId root) const {
        return hasBooleanAlternatives(terms, std::span<const ExprId>(&root, 1));
    }
};
}

TEST_CASE("Boolean alternatives: polarity distinguishes conjunctions and choices") {
    BooleanStructureFixture f;
    const auto a = f.variable("a"), b = f.variable("b");
    const auto both = f.node(Kind::And, {a, b}), either = f.node(Kind::Or, {a, b});
    CHECK_FALSE(f.alternatives(both));
    CHECK_FALSE(f.alternatives(f.node(Kind::Not, {either})));
    CHECK(f.alternatives(either));
    CHECK(f.alternatives(f.node(Kind::Not, {both})));
    CHECK(f.alternatives(f.node(Kind::And, {both, either})));
}

TEST_CASE("Boolean alternatives: negated implication fixes all antecedents") {
    BooleanStructureFixture f;
    const auto a = f.variable("a"), b = f.variable("b"), c = f.variable("c");
    const auto implication = f.node(Kind::Implies, {a, b, c});
    CHECK(f.alternatives(implication));
    CHECK_FALSE(f.alternatives(f.node(Kind::Not, {implication})));
    CHECK(f.alternatives(f.node(Kind::Not, {
        f.node(Kind::Implies, {f.node(Kind::Or, {a, b}), c})})));
}

TEST_CASE("Boolean alternatives: theory atoms remain indivisible") {
    BooleanStructureFixture f;
    const auto x = f.variable("x", 1), y = f.variable("y", 1);
    const auto a = f.variable("a"), b = f.variable("b");
    CHECK_FALSE(f.alternatives(f.node(Kind::Eq, {x, y})));
    CHECK_FALSE(f.alternatives(f.node(Kind::Not, {f.node(Kind::Distinct, {x, y})})));
    CHECK(f.alternatives(f.node(Kind::Eq, {a, b})));
    CHECK(f.alternatives(f.node(Kind::Distinct, {a, b})));
    CHECK(f.alternatives(f.node(Kind::Xor, {a, b})));
    CHECK(f.alternatives(f.node(Kind::Ite, {a, b, a})));
}

TEST_CASE("Boolean alternatives: deep shared formulas retain both polarities") {
    BooleanStructureFixture f;
    const auto a = f.variable("a"), b = f.variable("b");
    const auto either = f.node(Kind::Or, {a, b});
    auto root = f.node(Kind::Not, {either});
    for (size_t i = 0; i < 50000; ++i) root = f.node(Kind::Not, {root});
    CHECK_FALSE(f.alternatives(root));
    CHECK(f.alternatives(f.node(Kind::And, {either, root})));
    CHECK_FALSE(hasBooleanAlternatives(f.terms, {}));
}
