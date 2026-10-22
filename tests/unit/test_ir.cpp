#include <doctest/doctest.h>
#include "ir/NativeTerms.h"
#include <somtparser/frontend/parser.h>
#include <somtparser/ir/node.h>

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
    CHECK(terms.native(id) == sum);
}
