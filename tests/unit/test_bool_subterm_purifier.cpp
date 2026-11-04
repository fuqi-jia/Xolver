#include <doctest/doctest.h>
#include "frontend/preprocess/BoolSubtermPurifier.h"

using namespace xolver;

TEST_CASE("native Boolean purification keeps Boolean comparisons logical") {
    for (auto connective : {Kind::Eq, Kind::Distinct}) {
        NativeTerms terms;
        terms.registerSort(0, SortKind::Bool);
        terms.registerSort(1, SortKind::Int);
        auto p = terms.add({Kind::Variable, 0, {}, Payload(std::string("p"))});
        auto q = terms.add({Kind::Variable, 0, {}, Payload(std::string("q"))});
        auto x = terms.add({Kind::Variable, 1, {}, Payload(std::string("x"))});
        auto y = terms.add({Kind::Variable, 1, {}, Payload(std::string("y"))});
        auto comparison = terms.add({Kind::Leq, 0, {x, y}, {}});
        auto notQ = terms.add({Kind::Not, 0, {q}, {}});
        auto conjunction = terms.add({Kind::And, 0, {comparison, notQ}, {}});
        auto root = terms.add({connective, 0, {p, conjunction}, {}});
        terms.addAssertion(p);
        terms.pushScope();
        terms.addAssertion(q);
        terms.pushScope();
        terms.addAssertion(root);
        const auto size = terms.size();
        const auto scoped = terms.getScopedAssertions();
        BoolSubtermPurifier purifier(terms);
        CHECK_FALSE(purifier.run());
        purifier.commit();
        CHECK(terms.size() == size);
        CHECK(terms.getScopedAssertions() == scoped);
        terms.popScope();
        CHECK((terms.assertions() == std::vector<ExprId>{p, q}));
        terms.popScope();
        CHECK(terms.assertions() == std::vector<ExprId>{p});
    }
}

TEST_CASE("native Boolean purification preserves a logical comparison shared with a UF argument") {
    for (auto connective : {Kind::Eq, Kind::Distinct}) for (bool formulaFirst : {false, true}) {
        NativeTerms terms;
        terms.registerSort(0, SortKind::Bool);
        terms.registerSort(1, SortKind::Int);
        auto p = terms.add({Kind::Variable, 0, {}, Payload(std::string("p"))});
        auto x = terms.add({Kind::Variable, 1, {}, Payload(std::string("x"))});
        auto y = terms.add({Kind::Variable, 1, {}, Payload(std::string("y"))});
        auto comparison = terms.add({Kind::Lt, 0, {x, y}, {}});
        auto logical = terms.add({connective, 0, {p, comparison}, {}});
        auto call = terms.add({Kind::UFApply, 0, {comparison}, Payload(std::string("Q"))});
        terms.addAssertion(formulaFirst ? logical : call);
        terms.addAssertion(formulaFirst ? call : logical);
        BoolSubtermPurifier purifier(terms);
        REQUIRE(purifier.run());
        purifier.commit();
        const auto roots = terms.assertions();
        REQUIRE(roots.size() == 3);
        CHECK(roots[formulaFirst ? 0 : 1] == logical);
        const auto application = terms.get(roots[formulaFirst ? 1 : 0]);
        REQUIRE(application.kind == Kind::UFApply);
        const auto variable = application.children[0];
        CHECK(terms.get(variable).kind == Kind::Variable);
        const auto definition = terms.get(roots.back());
        CHECK(definition.kind == Kind::Eq);
        CHECK((definition.children == SmallVector<ExprId, 4>{variable, comparison}));
        const auto scoped = terms.getScopedAssertions();
        const auto size = terms.size();
        CHECK_FALSE(purifier.run());
        purifier.commit();
        CHECK(terms.getScopedAssertions() == scoped);
        CHECK(terms.size() == size);
    }
}

TEST_CASE("native Boolean purification retains parent definitions shared through child scopes") {
    NativeTerms terms;
    terms.registerSort(0, SortKind::Bool);
    auto p = terms.add({Kind::Variable, 0, {}, Payload(std::string("p"))});
    auto q = terms.add({Kind::Variable, 0, {}, Payload(std::string("q"))});
    auto notQ = terms.add({Kind::Not, 0, {q}, {}});
    auto argument = terms.add({Kind::And, 0, {p, notQ}, {}});
    auto parentCall = terms.add({Kind::UFApply, 0, {argument}, Payload(std::string("P"))});
    auto childCall = terms.add({Kind::UFApply, 0, {argument}, Payload(std::string("Q"))});
    terms.pushScope();
    // Child-first source order must not determine a shared definition's scope.
    terms.addAssertion(childCall);
    terms.addAssertion(parentCall, 0);
    BoolSubtermPurifier purifier(terms);
    REQUIRE(purifier.run());
    purifier.commit();
    const auto roots = terms.getScopedAssertions();
    REQUIRE(roots.size() == 4);
    CHECK(roots[0].first == 1);
    CHECK(roots[1].first == 0);
    CHECK(roots[2].first == 0);
    CHECK(roots[3].first == 0);
    const auto parent = roots[1].second;
    terms.popScope();
    const auto retained = terms.assertions();
    REQUIRE(retained.size() == 3);
    CHECK(retained.front() == parent);
    const auto variable = terms.get(parent).children[0];
    CHECK(terms.get(retained.back()).children[0] == variable);
}

TEST_CASE("native Boolean purification preserves formula context across stack growth") {
    NativeTerms terms;
    terms.registerSort(0, SortKind::Bool);
    TermExpr conjunction{Kind::And, 0, {}, {}};
    for (int i = 0; i < 1024; ++i) {
        auto variable = terms.add({Kind::Variable, 0, {},
            Payload(std::string("p") + std::to_string(i))});
        conjunction.children.push_back(terms.add({Kind::Not, 0, {variable}, {}}));
    }
    auto root = terms.add(std::move(conjunction));
    terms.addAssertion(root);
    auto size = terms.size();
    BoolSubtermPurifier purifier(terms);
    CHECK_FALSE(purifier.run());
    purifier.commit();
    CHECK(terms.size() == size);
    CHECK(terms.assertions() == std::vector<ExprId>{root});
}

TEST_CASE("native Boolean purification distinguishes shared formula and argument contexts") {
    for (bool formulaFirst : {false, true}) {
        CAPTURE(formulaFirst);
        NativeTerms terms;
        terms.registerSort(0, SortKind::Bool);
        auto variable = terms.add({Kind::Variable, 0, {}, Payload(std::string("p"))});
        auto negation = terms.add({Kind::Not, 0, {variable}, {}});
        auto call = terms.add({Kind::UFApply, 0, {negation}, Payload(std::string("Q"))});
        terms.addAssertion(formulaFirst ? negation : call);
        terms.addAssertion(formulaFirst ? call : negation);
        BoolSubtermPurifier purifier(terms);
        REQUIRE(purifier.run());
        purifier.commit();
        const auto roots = terms.assertions();
        REQUIRE(roots.size() == 3);
        CHECK(roots[formulaFirst ? 0 : 1] == negation);
        const auto application = terms.get(roots[formulaFirst ? 1 : 0]);
        REQUIRE(application.kind == Kind::UFApply);
        REQUIRE(application.children.size() == 1);
        const auto witness = application.children[0];
        CHECK(terms.get(witness).kind == Kind::Variable);
        const auto definition = terms.get(roots.back());
        CHECK(definition.kind == Kind::Distinct);
        CHECK((definition.children == SmallVector<ExprId, 4>{witness, variable}));
    }
}
