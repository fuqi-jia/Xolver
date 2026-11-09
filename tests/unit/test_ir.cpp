#include <doctest/doctest.h>
#include "ir/NativeTerms.h"
#include <somtparser/parser.h>
#include <utility>

using namespace xolver;

TEST_CASE("NativeTerms basic storage") {
    NativeTerms ir;
    ir.registerSort(0, SortKind::Bool);
    CHECK(ir.size() == 0);

    TermExpr e{Kind::ConstBool, 0, {}, Payload(true)};
    ExprId id = ir.add(e);
    CHECK(id == 0);
    CHECK(ir.size() == 1);
    CHECK(ir.get(id).kind == Kind::ConstBool);
}

TEST_CASE("native kind and sort metadata preserve exact literal sorts and comparison direction") {
    NativeTerms terms;
    terms.registerSort(0, SortKind::Bool);
    terms.registerSort(1, SortKind::Int);
    terms.registerSort(2, SortKind::Real);
    const auto boolean = terms.add({Kind::ConstBool, 0, {}, Payload(true)});
    const auto integer = terms.add({Kind::ConstInt, 1, {},
        Payload(std::string("1606938044258990275541962092341162602522202993782792835301377"))});
    const auto fraction = terms.add({Kind::ConstReal, 2, {}, Payload(std::string("1/2"))});
    const auto variable = terms.add({Kind::Variable, 1, {}, Payload(std::string("x"))});
    const auto bound = terms.add({Kind::BoundVariable, 1, {}, Payload(std::string("x"))});
    const auto greater = terms.add({Kind::Gt, 0, {variable, integer}, {}});
    const auto greaterEqual = terms.add({Kind::Geq, 0, {variable, integer}, {}});
    CHECK(terms.kind(boolean) == Kind::ConstBool);
    CHECK(terms.kind(integer) == Kind::ConstInt);
    CHECK(terms.kind(fraction) == Kind::ConstReal);
    CHECK(terms.kind(variable) == Kind::Variable);
    CHECK(terms.kind(bound) == Kind::BoundVariable);
    CHECK(terms.kind(greater) == Kind::Lt);
    CHECK(terms.kind(greaterEqual) == Kind::Leq);
    CHECK(terms.sortKind(terms.sortId(boolean)) == SortKind::Bool);
    CHECK(terms.sortKind(terms.sortId(integer)) == SortKind::Int);
    CHECK(terms.sortKind(terms.sortId(fraction)) == SortKind::Real);
    CHECK(terms.sortKind(terms.sortId(variable)) == SortKind::Int);
    CHECK(terms.sortKind(terms.sortId(bound)) == SortKind::Int);
    CHECK(terms.sortKind(terms.sortId(greater)) == SortKind::Bool);
    CHECK(terms.sortKind(terms.sortId(greaterEqual)) == SortKind::Bool);
    for (const auto comparison : {greater, greaterEqual}) {
        const auto full = terms.get(comparison);
        REQUIRE(full.children.size() == 2);
        CHECK(full.children[0] == integer);
        CHECK(full.children[1] == variable);
    }
    CHECK(terms.get(greater).kind == Kind::Lt);
    CHECK(terms.get(greaterEqual).kind == Kind::Leq);
}

TEST_CASE("native kind and sort metadata survive let aliases, copied ownership and index growth") {
    NativeTerms survivor;
    ExprId root = NullExpr, application = NullExpr;
    SortId integerSort = NullSort;
    {
        SOMTParser::Parser parser;
        REQUIRE(parser.parseStr("(set-logic QF_UFLIA)(declare-const x Int)"
            "(declare-fun f (Int) Int)(assert (let ((a (f x))) (= a 7)))"));
        NativeTerms terms(parser.getNodeManager());
        root = terms.index(parser.getAssertions().at(0));
        CHECK(terms.kind(root) == Kind::Eq);
        const auto equation = terms.get(root);
        REQUIRE(equation.children.size() == 2);
        ExprId literal = NullExpr;
        for (const auto child : equation.children) {
            if (terms.native(child)->getKind() == SOMTParser::NODE_KIND::NT_UF_APPLY)
                application = child;
            else literal = child;
        }
        REQUIRE(application != NullExpr);
        REQUIRE(literal != NullExpr);
        CHECK(terms.kind(application) == Kind::UFApply);
        CHECK(terms.kind(literal) == Kind::ConstInt);
        integerSort = terms.sortId(application);
        CHECK(terms.sortKind(integerSort) == SortKind::Int);
        CHECK(terms.sortKind(terms.sortId(root)) == SortKind::Bool);
        CHECK(terms.sortKind(terms.sortId(literal)) == SortKind::Int);
        survivor = terms;
    }
    CHECK(survivor.kind(root) == Kind::Eq);
    CHECK(survivor.kind(application) == Kind::UFApply);
    CHECK(survivor.sortId(application) == integerSort);
    auto moved = std::move(survivor);
    const auto fresh = moved.makeFreshVariable(integerSort, "fresh");
    CHECK(moved.kind(fresh) == Kind::Variable);
    CHECK(moved.kind(root) == Kind::Eq);
    CHECK(moved.kind(application) == Kind::UFApply);
    CHECK(moved.sortId(application) == integerSort);
    CHECK(moved.sortKind(moved.sortId(root)) == SortKind::Bool);
    CHECK(moved.sortKind(moved.sortId(fresh)) == SortKind::Int);
    CHECK_THROWS_AS(moved.kind(static_cast<ExprId>(moved.size())), std::out_of_range);
    CHECK_THROWS_AS(moved.sortId(static_cast<ExprId>(moved.size())), std::out_of_range);
}

TEST_CASE("NativeTerms scope management") {
    NativeTerms ir;
    ir.registerSort(0, SortKind::Bool);

    ir.addAssertion(ir.add(TermExpr{Kind::ConstBool, 0, {}, Payload(true)}));
    CHECK(ir.assertions().size() == 1);
    CHECK(ir.currentScopeLevel() == 0);

    ir.pushScope();
    CHECK(ir.currentScopeLevel() == 1);
    ir.addAssertion(ir.add(TermExpr{Kind::ConstBool, 0, {}, Payload(false)}));
    CHECK(ir.assertions().size() == 2);

    ir.pushScope();
    ir.addAssertion(ir.add(TermExpr{Kind::Variable, 0, {}, Payload(std::string("x"))}));
    CHECK(ir.assertions().size() == 3);

    ir.popScope();
    CHECK(ir.currentScopeLevel() == 1);
    CHECK(ir.assertions().size() == 2);

    ir.popScope();
    CHECK(ir.currentScopeLevel() == 0);
    CHECK(ir.assertions().size() == 1);

    // Pop at root is a no-op
    ir.popScope();
    CHECK(ir.currentScopeLevel() == 0);
    CHECK(ir.assertions().size() == 1);
}

TEST_CASE("native term indexing preserves parser node identity and immutable views") {
    SOMTParser::Parser parser;
    REQUIRE(parser.parseStr("(set-logic QF_LIA)(declare-const x Int)"
        "(assert (= (+ x 1) 7))"));
    auto root = parser.getAssertions().at(0);
    NativeTerms terms(parser.getNodeManager());
    auto id = terms.index(root);
    CHECK(terms.native(id) == root);
    auto size = terms.size();
    CHECK(terms.index(root) == id);
    CHECK(terms.size() == size);
    auto view = terms.get(id);
    auto children = view.children;
    view.children.clear();
    CHECK(terms.get(id).children == children);
    for (auto child : terms.get(id).children) CHECK(child < id);
    // The index owns native handles independently of the parser lifetime.
    NativeTerms copy = terms;
    terms = NativeTerms{};
    CHECK(copy.native(id) == root);
    CHECK(copy.get(id).children == children);
}

TEST_CASE("native terms keep distinct declarations and share explicit derived nodes") {
    NativeTerms terms;
    terms.registerSort(0, SortKind::Int);
    auto a = terms.add({Kind::BoundVariable, 0, {}, Payload(std::string("x"))});
    auto b = terms.add({Kind::BoundVariable, 0, {}, Payload(std::string("x"))});
    CHECK(a != b);
    CHECK(terms.native(a) != terms.native(b));
    auto one = terms.add({Kind::ConstInt, 0, {}, Payload(int64_t{1})});
    auto sum = terms.addShared({Kind::Add, 0, {a, one}, {}});
    CHECK(terms.addShared({Kind::Add, 0, {a, one}, {}}) == sum);
    CHECK(terms.addShared({Kind::Add, 0, {b, one}, {}}) != sum);
}

TEST_CASE("native handles survive manager release and deep DAG destruction") {
    SOMTParser::Node root;
    {
        auto manager = std::make_shared<SOMTParser::NodeManager>();
        auto leaf = manager->createNode(SOMTParser::SortManager::getBool(), true);
        root = manager->createNode(SOMTParser::SortManager::getBool(),
            SOMTParser::NODE_KIND::NT_NOT, "not", std::vector<SOMTParser::Node>{leaf});
        manager->clear();
        REQUIRE(root->getChildrenSize() == 1);
    }
    REQUIRE(root->getChildrenSize() == 1);
    auto boolean = SOMTParser::SortManager::getBool();
    for (size_t i = 0; i < 50000; ++i)
        root = std::make_shared<SOMTParser::DAGNode>(boolean,
            SOMTParser::NODE_KIND::NT_NOT, "not", std::vector<SOMTParser::Node>{root});
    root.reset(); // Must not consume one native stack frame per node.
}

TEST_CASE("native construction rejects missing sorts before creating a node") {
    NativeTerms terms;
    CHECK_THROWS_AS(terms.add({Kind::ConstInt, NullSort, {}, Payload(int64_t{1})}),
                    std::invalid_argument);
    CHECK_THROWS_AS(terms.addShared({Kind::Variable, 47, {}, Payload(std::string("x"))}),
                    std::invalid_argument);
    CHECK(terms.size() == 0);
    // The parser's public DAG API also permits unsorted placeholder nodes.
    auto placeholder = std::make_shared<SOMTParser::DAGNode>(
        nullptr, SOMTParser::NODE_KIND::NT_UNKNOWN, "placeholder");
    CHECK_NOTHROW(placeholder->hashCode());
}

TEST_CASE("native structural equality is stack safe on deep shared DAGs") {
    auto boolean = SOMTParser::SortManager::getBool();
    auto a = std::make_shared<SOMTParser::DAGNode>(boolean, SOMTParser::NODE_KIND::NT_VAR, "p");
    auto b = std::make_shared<SOMTParser::DAGNode>(boolean, SOMTParser::NODE_KIND::NT_VAR, "p");
    for (size_t i = 0; i < 50000; ++i) {
        a = std::make_shared<SOMTParser::DAGNode>(boolean, SOMTParser::NODE_KIND::NT_AND,
            "and", std::vector<SOMTParser::Node>{a, a});
        b = std::make_shared<SOMTParser::DAGNode>(boolean, SOMTParser::NODE_KIND::NT_AND,
            "and", std::vector<SOMTParser::Node>{b, b});
    }
    CHECK(a->isEquivalentTo(b));
    CHECK_FALSE(a->isEquivalentTo(SOMTParser::Node{}));
}

TEST_CASE("native shared construction reuses parsed operator nodes") {
    SOMTParser::Parser parser;
    REQUIRE(parser.parseStr("(set-logic QF_LRA)"
        "(declare-const a Real)(declare-const b Real)"
        "(declare-const p Bool)"
        "(assert (< (+ a b) b))(assert (not p))"));
    NativeTerms terms(parser.getNodeManager());
    const auto root = terms.index(parser.getAssertions().at(0));
    terms.index(parser.getAssertions().at(1));
    const auto size = terms.size();
    for (ExprId id = 0; id < size; ++id) {
        const auto view = terms.get(id);
        if (view.isLeaf()) continue;
        CHECK(terms.addShared(view) == id);
    }
    CHECK(terms.size() == size);
    CHECK(terms.native(root) == parser.getAssertions().at(0));
}

TEST_CASE("native ambiguous numeral sorts preserve fractions and real division") {
    NativeTerms terms;
    auto ambiguous = SOMTParser::SortManager::getIntOrReal();
    auto half = std::make_shared<SOMTParser::DAGNode>(
        ambiguous, SOMTParser::NODE_KIND::NT_CONST, "1/2");
    auto one = std::make_shared<SOMTParser::DAGNode>(
        ambiguous, SOMTParser::NODE_KIND::NT_CONST, "1");
    auto sum = std::make_shared<SOMTParser::DAGNode>(
        ambiguous, SOMTParser::NODE_KIND::NT_ADD, "+", std::vector<SOMTParser::Node>{half, one});
    auto id = terms.index(sum);
    auto view = terms.get(id);
    REQUIRE(view.children.size() == 2);
    CHECK((terms.sortKind(view.sort) == SortKind::Real));
    CHECK(terms.get(view.children[0]).kind == Kind::ConstReal);
    CHECK(terms.get(view.children[1]).kind == Kind::ConstInt);
    CHECK(terms.kind(view.children[0]) == Kind::ConstReal);
    CHECK(terms.kind(view.children[1]) == Kind::ConstInt);
    CHECK(terms.native(id) == sum);
}
