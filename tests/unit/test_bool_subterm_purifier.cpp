#include <doctest/doctest.h>
#include "frontend/preprocess/BoolSubtermPurifier.h"

using namespace xolver;

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
