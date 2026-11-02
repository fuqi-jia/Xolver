#include <doctest/doctest.h>
#include "ir/TermFeatureIndex.h"

using namespace xolver;

namespace {
NativeTerms expressionSpace() {
    NativeTerms terms;
    terms.registerSort(0, SortKind::Int);
    terms.registerSort(1, SortKind::Bool);
    terms.setBoolSortId(1);
    return terms;
}
}

TEST_CASE("Term features: active roots and shared growth reuse immutable summaries") {
    auto terms = expressionSpace();
    const auto x = terms.add({Kind::Variable, 0, {}, Payload(std::string("x"))});
    const auto y = terms.add({Kind::Variable, 0, {}, Payload(std::string("y"))});
    const auto sum = terms.add({Kind::Add, 0, {x, y}, {}});
    terms.addAssertion(sum);
    TermFeatureIndex features(terms);
    CHECK(features.containsAny(terms.assertions(), {Kind::Add}));
    const auto work = features.visitedNodes();
    CHECK_FALSE(features.containsAny(terms.assertions(), {Kind::Mod, Kind::Ite, Kind::UFApply}));
    CHECK(features.visitedNodes() == work);

    terms.pushScope();
    const auto modulus = terms.add({Kind::Mod, 0, {sum, y}, {}});
    terms.addAssertion(modulus);
    CHECK(features.containsAny(terms.assertions(), {Kind::Mod}));
    CHECK(features.visitedNodes() == work + 1);
    terms.popScope();
    CHECK_FALSE(features.containsAny(terms.assertions(), {Kind::Mod}));
    CHECK(features.visitedNodes() == work + 1);
    terms.clearAssertions();
    CHECK_FALSE(features.containsAny(terms.assertions(), {Kind::Variable, Kind::Add}));
}

TEST_CASE("Term features: replacing an expression space invalidates overlapping handles") {
    auto terms = expressionSpace();
    auto x = terms.add({Kind::Variable, 0, {}, Payload(std::string("x"))});
    auto one = terms.add({Kind::ConstInt, 0, {}, Payload(int64_t(1))});
    terms.addAssertion(terms.add({Kind::Add, 0, {x, one}, {}}));
    TermFeatureIndex features(terms);
    REQUIRE(features.containsAny(terms.assertions(), {Kind::Add}));
    auto replacement = expressionSpace();
    x = replacement.add({Kind::Variable, 0, {}, Payload(std::string("x"))});
    one = replacement.add({Kind::ConstInt, 0, {}, Payload(int64_t(1))});
    replacement.addAssertion(replacement.add({Kind::Mod, 0, {x, one}, {}}));
    terms = replacement;
    CHECK(features.containsAny(terms.assertions(), {Kind::Mod}));
    CHECK_FALSE(features.containsAny(terms.assertions(), {Kind::Add}));
}

TEST_CASE("Term features: deep DAGs, empty queries and Boolean sentinels are safe") {
    auto terms = expressionSpace();
    auto root = terms.add({Kind::Variable, 0, {}, Payload(std::string("x"))});
    for (int i = 0; i < 12000; ++i) root = terms.add({Kind::Neg, 0, {root}, {}});
    TermFeatureIndex features(terms);
    const std::vector<ExprId> roots{root};
    CHECK(features.containsAny(roots, {Kind::Neg}));
    CHECK_FALSE(features.containsAny(roots, {Kind::Mod}));
    CHECK(features.visitedNodes() == 12001);
    CHECK_FALSE(features.containsAny(roots, {}));
    const std::vector<ExprId> sentinel{NullExpr, TrueSentinelExpr, FalseSentinelExpr};
    CHECK(features.containsAny(sentinel, {Kind::ConstBool}));
    CHECK_FALSE(features.containsAny(sentinel, {Kind::Ite}));
}
