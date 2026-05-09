#include <doctest/doctest.h>
#include "expr/ir.h"

using namespace nlcolver;

TEST_CASE("CoreIr basic storage") {
    CoreIr ir;
    CHECK(ir.size() == 0);

    CoreExpr e{Kind::ConstBool, 0, {}, Payload(true)};
    ExprId id = ir.add(e);
    CHECK(id == 0);
    CHECK(ir.size() == 1);
    CHECK(ir.get(id).kind == Kind::ConstBool);
}

TEST_CASE("CoreIr scope management") {
    CoreIr ir;

    ir.addAssertion(ir.add(CoreExpr{Kind::ConstBool, 0, {}, Payload(true)}));
    CHECK(ir.assertions().size() == 1);
    CHECK(ir.currentScopeLevel() == 0);

    ir.pushScope();
    CHECK(ir.currentScopeLevel() == 1);
    ir.addAssertion(ir.add(CoreExpr{Kind::ConstBool, 0, {}, Payload(false)}));
    CHECK(ir.assertions().size() == 2);

    ir.pushScope();
    ir.addAssertion(ir.add(CoreExpr{Kind::Variable, 0, {}, Payload(std::string("x"))}));
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
