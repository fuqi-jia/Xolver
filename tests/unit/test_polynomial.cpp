#include <gmpxx.h>
#include <doctest/doctest.h>
#include "theory/arith/poly/PolynomialKernel.h"
#include "theory/arith/poly/PolynomialConverter.h"
#include "theory/arith/poly/RationalPolynomial.h"
#include "expr/ir.h"

using namespace nlcolver;

// ============================================================================
// PolynomialKernel basics
// ============================================================================

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

    PolyId xy = kernel->add(x, y);
    CHECK(!kernel->isConstant(xy));

    PolyId x2 = kernel->mul(x, x);
    CHECK(!kernel->isConstant(x2));

    PolyId x0 = kernel->add(x, zero);
    CHECK(kernel->eq(x0, x));

    PolyId x1 = kernel->mul(x, one);
    CHECK(kernel->eq(x1, x));

    PolyId xx = kernel->sub(x, x);
    CHECK(kernel->isZero(xx));

    PolyId nx = kernel->neg(x);
    PolyId nnx = kernel->neg(nx);
    CHECK(kernel->eq(nnx, x));

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

TEST_CASE("PolynomialKernel: mkConst rejects non-integer rationals") {
    auto kernel = createPolynomialKernel();

    PolyId bad = kernel->mkConst(mpq_class(3, 2));
    CHECK(bad == NullPoly);

    PolyId half = kernel->mkConst(mpq_class(1, 2));
    CHECK(half == NullPoly);

    PolyId ok = kernel->mkConst(mpq_class(2));
    REQUIRE(ok != NullPoly);
    CHECK(kernel->isConstant(ok));
    CHECK(kernel->toConstant(ok) == mpq_class(2));
}

// ============================================================================
// RationalPolynomial
// ============================================================================

TEST_CASE("RationalPolynomial: constant and variable") {
    auto p1 = RationalPolynomial::fromConstant(mpq_class(3, 2));
    CHECK(!p1.isZero());
    CHECK(p1.isConstant());
    CHECK(p1.constantValue() == mpq_class(3, 2));

    // VarId must be created through a kernel to be valid for mkVar later.
    // Here we just test the RationalPolynomial structure.
    auto p2 = RationalPolynomial::fromVar(VarId(0), 1, mpq_class(1));
    CHECK(!p2.isZero());
    CHECK(!p2.isConstant());
}

TEST_CASE("RationalPolynomial: addition and subtraction") {
    auto a = RationalPolynomial::fromConstant(mpq_class(1, 2));
    auto b = RationalPolynomial::fromConstant(mpq_class(1, 3));
    auto s = a + b;
    CHECK(s.isConstant());
    CHECK(s.constantValue() == mpq_class(5, 6));

    auto d = a - b;
    CHECK(d.isConstant());
    CHECK(d.constantValue() == mpq_class(1, 6));
}

TEST_CASE("RationalPolynomial: multiplication") {
    auto x = RationalPolynomial::fromVar(VarId(10), 1, mpq_class(1));
    auto y = RationalPolynomial::fromVar(VarId(20), 1, mpq_class(1));
    auto xy = x * y;
    CHECK(!xy.isConstant());
    CHECK(xy.terms().size() == 1);
    CHECK(xy.terms().begin()->first == MonomialKey{{VarId(10), 1}, {VarId(20), 1}});
    CHECK(xy.terms().begin()->second == mpq_class(1));
}

TEST_CASE("RationalPolynomial: power") {
    auto x = RationalPolynomial::fromVar(VarId(5), 1, mpq_class(1));
    auto x2 = x.pow(2);
    CHECK(x2.terms().size() == 1);
    CHECK(x2.terms().begin()->first == MonomialKey{{VarId(5), 2}});

    auto x3 = x.pow(3);
    CHECK(x3.terms().begin()->first == MonomialKey{{VarId(5), 3}});
}

TEST_CASE("RationalPolynomial: toPrimitiveInteger basic") {
    auto kernel = createPolynomialKernel();
    VarId xv = kernel->getOrCreateVar("x");
    VarId yv = kernel->getOrCreateVar("y");

    // 1/2*x + 1/3*y
    auto rp = RationalPolynomial::fromVar(xv, 1, mpq_class(1, 2));
    rp.addVar(yv, 1, mpq_class(1, 3));

    auto norm = rp.toPrimitiveInteger(*kernel);
    REQUIRE(norm.ok());
    // scale = g/D = 1/6
    CHECK(norm.scale == mpq_class(1, 6));
    // poly should be 3x + 2y
    auto valOpt = kernel->evalIntegerVarId(norm.poly, {{xv, 2}, {yv, 3}});
    REQUIRE(valOpt.has_value());
    CHECK(*valOpt == 12);  // 3*2 + 2*3 = 12
    // original = scale * poly = (1/6) * 12 = 2
    // verify: (1/2)*2 + (1/3)*3 = 1 + 1 = 2
}

TEST_CASE("RationalPolynomial: toPrimitiveInteger with content gcd") {
    auto kernel = createPolynomialKernel();
    VarId xv = kernel->getOrCreateVar("x");
    VarId yv = kernel->getOrCreateVar("y");

    // 2/6*x + 4/6*y = (1/3)x + (2/3)y
    auto rp = RationalPolynomial::fromVar(xv, 1, mpq_class(2, 6));
    rp.addVar(yv, 1, mpq_class(4, 6));

    auto norm = rp.toPrimitiveInteger(*kernel);
    REQUIRE(norm.ok());
    // D = 6, D*p = 2x + 4y, g = 2, scale = 2/6 = 1/3
    CHECK(norm.scale == mpq_class(1, 3));
    // poly should be x + 2y
    auto valOpt = kernel->evalIntegerVarId(norm.poly, {{xv, 2}, {yv, 3}});
    REQUIRE(valOpt.has_value());
    CHECK(*valOpt == 8);  // 2 + 6 = 8
}

TEST_CASE("RationalPolynomial: toPrimitiveInteger negative coefficients") {
    auto kernel = createPolynomialKernel();
    VarId xv = kernel->getOrCreateVar("x");

    // -1/2*x + 1
    auto rp = RationalPolynomial::fromVar(xv, 1, mpq_class(-1, 2));
    rp.addConstant(mpq_class(1));

    auto norm = rp.toPrimitiveInteger(*kernel);
    REQUIRE(norm.ok());
    // scale > 0 regardless of sign
    CHECK(norm.scale > 0);
}

// ============================================================================
// PolynomialConverter
// ============================================================================

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
    auto res = conv.convert(addExpr, ir);

    CHECK(res.ok());
    CHECK(res.scale == 1);
    CHECK(!kernel->isConstant(res.poly));
    CHECK(!kernel->isZero(res.poly));
}

TEST_CASE("PolynomialConverter: power expression") {
    CoreIr ir;

    ExprId x = ir.add(CoreExpr{Kind::Variable, 0, {}, Payload(std::string("x"))});
    ExprId two = ir.add(CoreExpr{Kind::ConstInt, 0, {}, Payload(int64_t(2))});
    ExprId powExpr = ir.add(CoreExpr{Kind::Pow, 0, {x, two}, {}});

    auto kernel = createPolynomialKernel();
    PolynomialConverter conv(*kernel);
    auto res = conv.convert(powExpr, ir);

    CHECK(res.ok());
    CHECK(res.scale == 1);
    CHECK(!kernel->isConstant(res.poly));
}

TEST_CASE("PolynomialConverter: rational coefficient denominator clearing") {
    CoreIr ir;

    // Build: (1/2)*x + y  ->  scale 1/2? No, primitive integer: x + 2y, scale 1/2
    ExprId x = ir.add(CoreExpr{Kind::Variable, 0, {}, Payload(std::string("x"))});
    ExprId y = ir.add(CoreExpr{Kind::Variable, 0, {}, Payload(std::string("y"))});
    ExprId half = ir.add(CoreExpr{Kind::ConstReal, 0, {}, Payload(std::string("1/2"))});

    ExprId mul1 = ir.add(CoreExpr{Kind::Mul, 0, {half, x}, {}});
    ExprId addExpr = ir.add(CoreExpr{Kind::Add, 0, {mul1, y}, {}});

    auto kernel = createPolynomialKernel();
    PolynomialConverter conv(*kernel);
    auto res = conv.convert(addExpr, ir);

    CHECK(res.ok());
    // (1/2)x + y = (1/2)(x + 2y)  ->  scale = 1/2
    CHECK(res.scale == mpq_class(1, 2));
    CHECK(!kernel->isConstant(res.poly));

    // Verify: poly at (x=2, y=1) -> x + 2y = 4
    auto valOpt = kernel->evalIntegerVarId(res.poly, {{kernel->getOrCreateVar("x"), 2}, {kernel->getOrCreateVar("y"), 1}});
    REQUIRE(valOpt.has_value());
    CHECK(*valOpt == 4);
    // original = scale * poly = (1/2) * 4 = 2
    // (1/2)*2 + 1 = 2  ✓
}

TEST_CASE("PolynomialConverter: mixed rational and integer coefficients") {
    CoreIr ir;

    // Build: (1/2)*x + (1/3)*y  ->  primitive: 3x + 2y, scale = 1/6
    ExprId x = ir.add(CoreExpr{Kind::Variable, 0, {}, Payload(std::string("x"))});
    ExprId y = ir.add(CoreExpr{Kind::Variable, 0, {}, Payload(std::string("y"))});
    ExprId half = ir.add(CoreExpr{Kind::ConstReal, 0, {}, Payload(std::string("1/2"))});
    ExprId third = ir.add(CoreExpr{Kind::ConstReal, 0, {}, Payload(std::string("1/3"))});

    ExprId mul1 = ir.add(CoreExpr{Kind::Mul, 0, {half, x}, {}});
    ExprId mul2 = ir.add(CoreExpr{Kind::Mul, 0, {third, y}, {}});
    ExprId addExpr = ir.add(CoreExpr{Kind::Add, 0, {mul1, mul2}, {}});

    auto kernel = createPolynomialKernel();
    PolynomialConverter conv(*kernel);
    auto res = conv.convert(addExpr, ir);

    CHECK(res.ok());
    CHECK(res.scale == mpq_class(1, 6));

    auto valOpt = kernel->evalIntegerVarId(res.poly, {{kernel->getOrCreateVar("x"), 2}, {kernel->getOrCreateVar("y"), 3}});
    REQUIRE(valOpt.has_value());
    CHECK(*valOpt == 12);  // 3*2 + 2*3 = 12
}

TEST_CASE("PolynomialConverter: rational coefficient in power") {
    CoreIr ir;

    // Build: ((1/2)*x)^2  ->  (1/4)*x^2  ->  primitive: x^2, scale = 1/4
    ExprId x = ir.add(CoreExpr{Kind::Variable, 0, {}, Payload(std::string("x"))});
    ExprId half = ir.add(CoreExpr{Kind::ConstReal, 0, {}, Payload(std::string("1/2"))});
    ExprId two = ir.add(CoreExpr{Kind::ConstInt, 0, {}, Payload(int64_t(2))});

    ExprId mul1 = ir.add(CoreExpr{Kind::Mul, 0, {half, x}, {}});
    ExprId powExpr = ir.add(CoreExpr{Kind::Pow, 0, {mul1, two}, {}});

    auto kernel = createPolynomialKernel();
    PolynomialConverter conv(*kernel);
    auto res = conv.convert(powExpr, ir);

    CHECK(res.ok());
    CHECK(res.scale == mpq_class(1, 4));

    auto valOpt = kernel->evalIntegerVarId(res.poly, {{kernel->getOrCreateVar("x"), 2}});
    REQUIRE(valOpt.has_value());
    CHECK(*valOpt == 4);  // x^2 = 4
    // original = (1/4) * 4 = 1  ✓
}

TEST_CASE("PolynomialConverter: constraint conversion") {
    CoreIr ir;

    // Build constraint: (1/2)*x + y = 1
    // diff = (1/2)*x + y - 1  ->  primitive: x + 2y - 2, scale = 1/2
    ExprId x = ir.add(CoreExpr{Kind::Variable, 0, {}, Payload(std::string("x"))});
    ExprId y = ir.add(CoreExpr{Kind::Variable, 0, {}, Payload(std::string("y"))});
    ExprId half = ir.add(CoreExpr{Kind::ConstReal, 0, {}, Payload(std::string("1/2"))});
    ExprId one = ir.add(CoreExpr{Kind::ConstInt, 0, {}, Payload(int64_t(1))});

    ExprId mul1 = ir.add(CoreExpr{Kind::Mul, 0, {half, x}, {}});
    ExprId lhs = ir.add(CoreExpr{Kind::Add, 0, {mul1, y}, {}});

    auto kernel = createPolynomialKernel();
    PolynomialConverter conv(*kernel);
    auto cc = conv.convertConstraint(lhs, one, Relation::Eq, ir);

    CHECK(cc.isConstraint());
    CHECK(!kernel->isConstant(cc.diff));

    // Verify diff at (x=2, y=0): x + 2y - 2 = 0
    auto valOpt = kernel->evalIntegerVarId(cc.diff, {{kernel->getOrCreateVar("x"), 2}, {kernel->getOrCreateVar("y"), 0}});
    REQUIRE(valOpt.has_value());
    CHECK(*valOpt == 0);
}

TEST_CASE("PolynomialConverter: zero polynomial simplification") {
    CoreIr ir;
    auto kernel = createPolynomialKernel();
    PolynomialConverter conv(*kernel);

    ExprId x = ir.add(CoreExpr{Kind::Variable, 0, {}, Payload(std::string("x"))});

    // x - x = 0  ->  tautology for Eq/Leq/Geq, conflict for Neq/Lt/Gt
    ExprId subExpr = ir.add(CoreExpr{Kind::Sub, 0, {x, x}, {}});

    // diff = (x-x) - (x-x) = 0
    auto ccEq  = conv.convertConstraint(subExpr, subExpr, Relation::Eq, ir);
    CHECK(ccEq.status == PolyConstraintStatus::Tautology);

    auto ccNeq = conv.convertConstraint(subExpr, subExpr, Relation::Neq, ir);
    CHECK(ccNeq.status == PolyConstraintStatus::Conflict);

    auto ccLt  = conv.convertConstraint(subExpr, subExpr, Relation::Lt, ir);
    CHECK(ccLt.status == PolyConstraintStatus::Conflict);

    auto ccLeq = conv.convertConstraint(subExpr, subExpr, Relation::Leq, ir);
    CHECK(ccLeq.status == PolyConstraintStatus::Tautology);

    auto ccGt  = conv.convertConstraint(subExpr, subExpr, Relation::Gt, ir);
    CHECK(ccGt.status == PolyConstraintStatus::Conflict);

    auto ccGeq = conv.convertConstraint(subExpr, subExpr, Relation::Geq, ir);
    CHECK(ccGeq.status == PolyConstraintStatus::Tautology);
}

TEST_CASE("PolynomialConverter: division by numeric constant") {
    CoreIr ir;
    auto kernel = createPolynomialKernel();
    PolynomialConverter conv(*kernel);

    // (x + y) / 3  ->  (1/3)x + (1/3)y  ->  primitive: x + y, scale = 1/3
    ExprId x = ir.add(CoreExpr{Kind::Variable, 0, {}, Payload(std::string("x"))});
    ExprId y = ir.add(CoreExpr{Kind::Variable, 0, {}, Payload(std::string("y"))});
    ExprId three = ir.add(CoreExpr{Kind::ConstInt, 0, {}, Payload(int64_t(3))});
    ExprId addExpr = ir.add(CoreExpr{Kind::Add, 0, {x, y}, {}});
    ExprId divExpr = ir.add(CoreExpr{Kind::Div, 0, {addExpr, three}, {}});

    auto res = conv.convert(divExpr, ir);
    CHECK(res.ok());
    CHECK(res.scale == mpq_class(1, 3));

    // Verify: poly at (x=3, y=3) = 6
    auto valOpt = kernel->evalIntegerVarId(res.poly, {{kernel->getOrCreateVar("x"), 3}, {kernel->getOrCreateVar("y"), 3}});
    REQUIRE(valOpt.has_value());
    CHECK(*valOpt == 6);
    // original = (1/3) * 6 = 2  ✓  ((3+3)/3 = 2)
}

TEST_CASE("PolynomialConverter: division by variable is unsupported") {
    CoreIr ir;
    auto kernel = createPolynomialKernel();
    PolynomialConverter conv(*kernel);

    // 2 / x  ->  unsupported non-polynomial
    ExprId x = ir.add(CoreExpr{Kind::Variable, 0, {}, Payload(std::string("x"))});
    ExprId two = ir.add(CoreExpr{Kind::ConstInt, 0, {}, Payload(int64_t(2))});
    ExprId divExpr = ir.add(CoreExpr{Kind::Div, 0, {two, x}, {}});

    auto res = conv.convert(divExpr, ir);
    CHECK(!res.ok());
}

TEST_CASE("PolynomialConverter: power expansion") {
    CoreIr ir;
    auto kernel = createPolynomialKernel();
    PolynomialConverter conv(*kernel);

    // (x + y)^2  ->  x^2 + 2xy + y^2
    ExprId x = ir.add(CoreExpr{Kind::Variable, 0, {}, Payload(std::string("x"))});
    ExprId y = ir.add(CoreExpr{Kind::Variable, 0, {}, Payload(std::string("y"))});
    ExprId two = ir.add(CoreExpr{Kind::ConstInt, 0, {}, Payload(int64_t(2))});
    ExprId addExpr = ir.add(CoreExpr{Kind::Add, 0, {x, y}, {}});
    ExprId powExpr = ir.add(CoreExpr{Kind::Pow, 0, {addExpr, two}, {}});

    auto res = conv.convert(powExpr, ir);
    CHECK(res.ok());
    CHECK(res.scale == 1);

    // Verify: at (x=2, y=3): 4 + 12 + 9 = 25
    auto valOpt = kernel->evalIntegerVarId(res.poly, {{kernel->getOrCreateVar("x"), 2}, {kernel->getOrCreateVar("y"), 3}});
    REQUIRE(valOpt.has_value());
    CHECK(*valOpt == 25);
}

TEST_CASE("PolynomialConverter: power zero") {
    CoreIr ir;
    auto kernel = createPolynomialKernel();
    PolynomialConverter conv(*kernel);

    // (x + y)^0  ->  1
    ExprId x = ir.add(CoreExpr{Kind::Variable, 0, {}, Payload(std::string("x"))});
    ExprId y = ir.add(CoreExpr{Kind::Variable, 0, {}, Payload(std::string("y"))});
    ExprId zero = ir.add(CoreExpr{Kind::ConstInt, 0, {}, Payload(int64_t(0))});
    ExprId addExpr = ir.add(CoreExpr{Kind::Add, 0, {x, y}, {}});
    ExprId powExpr = ir.add(CoreExpr{Kind::Pow, 0, {addExpr, zero}, {}});

    auto res = conv.convert(powExpr, ir);
    CHECK(res.ok());
    CHECK(kernel->isConstant(res.poly));
    CHECK(kernel->toConstant(res.poly) == mpq_class(1));
}

// ============================================================================
// RationalPolynomial from PolyId and substituteRational
// ============================================================================

TEST_CASE("RationalPolynomial: fromPolyId roundtrip") {
    auto kernel = createPolynomialKernel();
    VarId xv = kernel->getOrCreateVar("x");
    VarId yv = kernel->getOrCreateVar("y");

    // Build integer poly: 3x + 2y via RationalPolynomial
    auto rp = RationalPolynomial::fromVar(xv, 1, mpq_class(3));
    rp.addVar(yv, 1, mpq_class(2));
    auto norm = rp.toPrimitiveInteger(*kernel);
    REQUIRE(norm.ok());

    // Reconstruct RationalPolynomial from PolyId
    auto rpOpt = RationalPolynomial::fromPolyId(norm.poly, *kernel);
    REQUIRE(rpOpt.has_value());
    CHECK(rpOpt->terms().size() == 2);
    CHECK(rpOpt->terms().at(MonomialKey{{xv, 1}}) == mpq_class(3));
    CHECK(rpOpt->terms().at(MonomialKey{{yv, 1}}) == mpq_class(2));
}

TEST_CASE("LibPolyKernel: substituteRational with rational result") {
    auto kernel = createPolynomialKernel();
    VarId xv = kernel->getOrCreateVar("x");
    VarId yv = kernel->getOrCreateVar("y");

    // Build: x*y - 1  (integer coefficients)
    auto rp = RationalPolynomial::fromVar(xv, 1, mpq_class(1));
    rp = rp * RationalPolynomial::fromVar(yv, 1, mpq_class(1));
    rp.addConstant(mpq_class(-1));
    auto norm = rp.toPrimitiveInteger(*kernel);
    REQUIRE(norm.ok());

    // Substitute x = 1/2  ->  (1/2)y - 1  ->  primitive: y - 2, scale = 1/2
    auto subOpt = kernel->substituteRational(norm.poly, xv, mpq_class(1, 2));
    REQUIRE(subOpt.has_value());

    // Verify: at y=2, substituted poly should be 0
    auto valOpt = kernel->evalIntegerVarId(*subOpt, {{yv, 2}});
    REQUIRE(valOpt.has_value());
    CHECK(*valOpt == 0);

    // Verify: at y=4, substituted poly should be 2
    auto valOpt2 = kernel->evalIntegerVarId(*subOpt, {{yv, 4}});
    REQUIRE(valOpt2.has_value());
    CHECK(*valOpt2 == 2);
}
