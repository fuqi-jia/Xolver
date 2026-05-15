#include <gmpxx.h>
#include <doctest/doctest.h>
#include "theory/arith/poly/PolynomialKernel.h"
#include "theory/arith/poly/PolynomialConverter.h"
#include "expr/ir.h"

using namespace nlcolver;

TEST_CASE("PolynomialKernel: basic arithmetic") {
    auto kernel = createPolynomialKernel();

    PolyId zero = kernel->mkZero();
    PolyId one  = kernel->mkOne();
    CHECK(kernel->isZero(zero));
    CHECK(kernel->isConstant(one));
    CHECK(!kernel->isZero(one));

    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    PolyId y = kernel->mkVar(kernel->getOrCreateVar("y"));

    CHECK(!kernel->isConstant(x));
    CHECK(!kernel->isZero(x));

    // x + y
    PolyId xy = kernel->add(x, y);
    CHECK(!kernel->isConstant(xy));

    // x * x = x^2
    PolyId x2 = kernel->mul(x, x);
    CHECK(!kernel->isConstant(x2));

    // x + 0 = x
    PolyId x0 = kernel->add(x, zero);
    CHECK(kernel->eq(x0, x));

    // x * 1 = x
    PolyId x1 = kernel->mul(x, one);
    CHECK(kernel->eq(x1, x));

    // x - x = 0
    PolyId xx = kernel->sub(x, x);
    CHECK(kernel->isZero(xx));

    // -(-x) = x
    PolyId nx = kernel->neg(x);
    PolyId nnx = kernel->neg(nx);
    CHECK(kernel->eq(nnx, x));

    // x^3
    PolyId x3 = kernel->pow(x, 3);
    CHECK(!kernel->isConstant(x3));
}

TEST_CASE("PolynomialKernel: constant extraction") {
    auto kernel = createPolynomialKernel();

    PolyId c = kernel->mkConst(mpq_class(42));
    CHECK(kernel->isConstant(c));
    mpq_class v = kernel->toConstant(c);
    CHECK(v.get_num().get_si() == 42);
    CHECK(v.get_den().get_si() == 1);
}

TEST_CASE("PolynomialConverter: linear expression") {
    CoreIr ir;

    // Build: 2*x + 3*y
    ExprId x = ir.add(CoreExpr{Kind::Variable, 0, {}, Payload(std::string("x"))});
    ExprId y = ir.add(CoreExpr{Kind::Variable, 0, {}, Payload(std::string("y"))});
    ExprId two = ir.add(CoreExpr{Kind::ConstInt, 0, {}, Payload(int64_t(2))});
    ExprId three = ir.add(CoreExpr{Kind::ConstInt, 0, {}, Payload(int64_t(3))});

    ExprId mul1 = ir.add(CoreExpr{Kind::Mul, 0, {two, x}, {}});
    ExprId mul2 = ir.add(CoreExpr{Kind::Mul, 0, {three, y}, {}});
    ExprId addExpr = ir.add(CoreExpr{Kind::Add, 0, {mul1, mul2}, {}});

    auto kernel = createPolynomialKernel();
    PolynomialConverter conv(*kernel);
    PolyId p = conv.convert(addExpr, ir);

    CHECK(p != NullPoly);
    CHECK(!kernel->isConstant(p));
    CHECK(!kernel->isZero(p));
}

TEST_CASE("PolynomialConverter: power expression") {
    CoreIr ir;

    // Build: x^2
    ExprId x = ir.add(CoreExpr{Kind::Variable, 0, {}, Payload(std::string("x"))});
    ExprId two = ir.add(CoreExpr{Kind::ConstInt, 0, {}, Payload(int64_t(2))});
    ExprId powExpr = ir.add(CoreExpr{Kind::Pow, 0, {x, two}, {}});

    auto kernel = createPolynomialKernel();
    PolynomialConverter conv(*kernel);
    PolyId p = conv.convert(powExpr, ir);

    CHECK(p != NullPoly);
    CHECK(!kernel->isConstant(p));
}
