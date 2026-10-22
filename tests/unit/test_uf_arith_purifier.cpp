#include <doctest/doctest.h>
#include "frontend/preprocess/UfInArithPurifier.h"
#include <set>

using namespace xolver;

TEST_CASE("native UF purification distinguishes arithmetic and uninterpreted contexts") {
    for (bool arithmeticFirst : {false, true}) {
        CAPTURE(arithmeticFirst);
        NativeTerms terms;
        terms.registerSort(0, SortKind::Real);
        terms.registerSort(1, SortKind::Bool);
        auto x = terms.add({Kind::Variable, 0, {}, Payload(std::string("x"))});
        auto call = terms.add({Kind::UFApply, 0, {x}, Payload(std::string("f"))});
        auto predicate = terms.add({Kind::UFApply, 1, {call}, Payload(std::string("p"))});
        auto sum = terms.add({Kind::Add, 0, {call, call}, {}});
        auto comparison = terms.add({Kind::Lt, 1, {sum, x}, {}});
        terms.addAssertion(arithmeticFirst ? comparison : predicate);
        terms.addAssertion(arithmeticFirst ? predicate : comparison);
        UfInArithPurifier pass(terms);
        REQUIRE(pass.run());
        pass.commit();
        const auto roots = terms.assertions();
        REQUIRE(roots.size() == 3);
        CHECK(roots[arithmeticFirst ? 1 : 0] == predicate);
        const auto rewritten = terms.get(roots[arithmeticFirst ? 0 : 1]);
        REQUIRE(rewritten.children.size() == 2);
        const auto addition = terms.get(rewritten.children[0]);
        REQUIRE(addition.kind == Kind::Add);
        REQUIRE(addition.children.size() == 2);
        CHECK(addition.children[0] == addition.children[1]);
        CHECK(terms.get(addition.children[0]).kind == Kind::Variable);
        const auto definition = terms.get(roots.back());
        CHECK(definition.kind == Kind::Eq);
        CHECK((definition.children == SmallVector<ExprId, 4>{addition.children[0], call}));
    }
}

TEST_CASE("native UF purification bridges every nary arithmetic operand") {
    NativeTerms terms;
    terms.registerSort(0, SortKind::Int);
    terms.registerSort(1, SortKind::Bool);
    auto x = terms.add({Kind::Variable, 0, {}, Payload(std::string("x"))});
    TermExpr addition{Kind::Add, 0, {}, {}};
    std::set<ExprId> originalCalls;
    for (int i = 0; i < 12; ++i) {
        auto call = terms.add({Kind::UFApply, 0, {x},
                              Payload(std::string("f") + std::to_string(i))});
        addition.children.push_back(call);
        originalCalls.insert(call);
    }
    auto sum = terms.add(std::move(addition));
    auto comparison = terms.add({Kind::Leq, 1, {sum, x}, {}});
    terms.addAssertion(comparison);
    UfInArithPurifier pass(terms);
    REQUIRE(pass.run());
    pass.commit();
    REQUIRE(terms.assertions().size() == 13);
    const auto rewritten = terms.get(terms.assertions().front());
    REQUIRE(rewritten.children.size() == 2);
    const auto operands = terms.get(rewritten.children[0]).children;
    REQUIRE(operands.size() == 12);
    std::set<ExprId> witnesses(operands.begin(), operands.end());
    CHECK(witnesses.size() == 12);
    for (auto variable : witnesses) CHECK(terms.get(variable).kind == Kind::Variable);
    for (size_t i = 1; i < terms.assertions().size(); ++i) {
        const auto definition = terms.get(terms.assertions()[i]);
        REQUIRE(definition.kind == Kind::Eq);
        REQUIRE(definition.children.size() == 2);
        CHECK(witnesses.erase(definition.children[0]) == 1);
        CHECK(originalCalls.erase(definition.children[1]) == 1);
    }
    CHECK(witnesses.empty());
    CHECK(originalCalls.empty());
}

TEST_CASE("native UF purification classifies comparison operands by their sorts") {
    for (Kind relation : {Kind::Eq, Kind::Distinct}) {
        for (SortKind sort : {SortKind::Int, SortKind::Real, SortKind::Bool}) {
            CAPTURE(static_cast<int>(relation));
            CAPTURE(static_cast<int>(sort));
            NativeTerms terms;
            terms.registerSort(0, sort);
            const SortId boolean = sort == SortKind::Bool ? 0 : 1;
            if (boolean != 0) terms.registerSort(boolean, SortKind::Bool);
            auto x = terms.add({Kind::Variable, 0, {}, Payload(std::string("x"))});
            auto call = terms.add({Kind::UFApply, 0, {x}, Payload(std::string("f"))});
            auto comparison = terms.add({relation, boolean, {call, x}, {}});
            terms.addAssertion(comparison);
            UfInArithPurifier pass(terms);
            CHECK(pass.run() == (sort != SortKind::Bool));
            pass.commit();
            if (sort == SortKind::Bool) {
                CHECK(terms.assertions() == std::vector<ExprId>{comparison});
            } else {
                REQUIRE(terms.assertions().size() == 2);
                const auto rewritten = terms.get(terms.assertions().front());
                REQUIRE(rewritten.children.size() == 2);
                CHECK(rewritten.kind == relation);
                CHECK(terms.get(rewritten.children[0]).kind == Kind::Variable);
                CHECK(rewritten.children[1] == x);
                const auto definition = terms.get(terms.assertions().back());
                REQUIRE(definition.children.size() == 2);
                CHECK(definition.children[1] == call);
            }
        }
    }
}
