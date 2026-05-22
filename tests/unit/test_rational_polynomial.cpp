// White-box: RationalPolynomial — the workhorse of CDCAC projection.
//
// These tests cover construction, normalization, algebraic ops, partial
// derivative, leading coefficient, content/primitive part, and pseudo-
// remainder. CDCAC correctness depends on these being exactly right.

#include <doctest/doctest.h>
#include <gmpxx.h>
#include "theory/arith/poly/RationalPolynomial.h"

using namespace nlcolver;

static VarId VX = VarId{1}, VY = VarId{2};

TEST_CASE("RatPoly: fromConstant + isConstant") {
    auto p = RationalPolynomial::fromConstant(mpq_class(7));
    CHECK(p.isConstant());
    CHECK(p.constantValue() == 7);
}

TEST_CASE("RatPoly: fromVar(x, 1, 1) = x") {
    auto x = RationalPolynomial::fromVar(VX, 1, 1);
    CHECK(!x.isConstant());
    CHECK(x.degree(VX) == 1);
    CHECK(x.contains(VX));
    CHECK(!x.contains(VY));
}

TEST_CASE("RatPoly: addTerm + normalize merges like terms") {
    RationalPolynomial p;
    p.addVar(VX, 2, 3);   // 3x²
    p.addVar(VX, 2, 4);   // +4x²
    p.normalize();
    CHECK(p.degree(VX) == 2);
    // Coefficient of x² is now 7.
    auto coeffs = p.coefficients(VX);
    REQUIRE(coeffs.size() >= 3);
    CHECK(coeffs[2].isConstant());
    CHECK(coeffs[2].constantValue() == 7);
}

TEST_CASE("RatPoly: degree of zero poly is -1") {
    RationalPolynomial zero;
    CHECK(zero.isZero());
    CHECK(zero.degree(VX) == -1);
}

TEST_CASE("RatPoly: derivative of x³ is 3x²") {
    RationalPolynomial p;
    p.addVar(VX, 3, 1);  // x³
    p.normalize();
    auto d = p.derivative(VX);
    CHECK(d.degree(VX) == 2);
    auto coeffs = d.coefficients(VX);
    CHECK(coeffs[2].isConstant());
    CHECK(coeffs[2].constantValue() == 3);
}

TEST_CASE("RatPoly: derivative of constant is zero") {
    auto c = RationalPolynomial::fromConstant(5);
    auto d = c.derivative(VX);
    CHECK(d.isZero());
}

TEST_CASE("RatPoly: leadingCoefficient of 2x² + 3x + 1 (in x) is 2") {
    RationalPolynomial p;
    p.addVar(VX, 2, 2);
    p.addVar(VX, 1, 3);
    p.addConstant(1);
    p.normalize();
    auto lc = p.leadingCoefficient(VX);
    CHECK(lc.isConstant());
    CHECK(lc.constantValue() == 2);
}

TEST_CASE("RatPoly: variables() returns set of appearing vars") {
    RationalPolynomial p;
    p.addVar(VX, 2, 1);
    p.addVar(VY, 1, 1);
    p.normalize();
    auto vs = p.variables();
    CHECK(vs.count(VX) == 1);
    CHECK(vs.count(VY) == 1);
}

TEST_CASE("RatPoly: substituteRational(x, 2) into x² + 1 gives 5") {
    RationalPolynomial p;
    p.addVar(VX, 2, 1);
    p.addConstant(1);
    p.normalize();
    auto r = p.substituteRational(VX, 2);
    CHECK(r.isConstant());
    CHECK(r.constantValue() == 5);
}

TEST_CASE("RatPoly: substitute zero into 3x + 4 gives 4") {
    RationalPolynomial p;
    p.addVar(VX, 1, 3);
    p.addConstant(4);
    p.normalize();
    auto r = p.substituteRational(VX, 0);
    CHECK(r.isConstant());
    CHECK(r.constantValue() == 4);
}

TEST_CASE("RatPoly: content(x) of 6x² + 9x + 12 is 3") {
    RationalPolynomial p;
    p.addVar(VX, 2, 6);
    p.addVar(VX, 1, 9);
    p.addConstant(12);
    p.normalize();
    auto c = p.content(VX);
    CHECK(c == 3);
}

TEST_CASE("RatPoly: primitivePart of 6x² + 9x + 12 is 2x² + 3x + 4") {
    RationalPolynomial p;
    p.addVar(VX, 2, 6);
    p.addVar(VX, 1, 9);
    p.addConstant(12);
    p.normalize();
    auto pp = p.primitivePart(VX);
    auto coeffs = pp.coefficients(VX);
    CHECK(coeffs[0].constantValue() == 4);
    CHECK(coeffs[1].constantValue() == 3);
    CHECK(coeffs[2].constantValue() == 2);
}

TEST_CASE("RatPoly: arithmetic — (x + 1)*(x - 1) = x² - 1") {
    auto x  = RationalPolynomial::fromVar(VX, 1, 1);
    auto one = RationalPolynomial::fromConstant(1);
    auto xp1 = x + one;
    auto xm1 = x - one;
    auto prod = xp1 * xm1;
    prod.normalize();
    auto coeffs = prod.coefficients(VX);
    REQUIRE(coeffs.size() >= 3);
    CHECK(coeffs[0].constantValue() == -1);
    CHECK(coeffs[1].constantValue() == 0);
    CHECK(coeffs[2].constantValue() == 1);
}

TEST_CASE("RatPoly: pow(x, 3) gives x³") {
    auto x = RationalPolynomial::fromVar(VX, 1, 1);
    auto x3 = x.pow(3);
    x3.normalize();
    CHECK(x3.degree(VX) == 3);
}

TEST_CASE("RatPoly: zero - zero is zero") {
    RationalPolynomial z;
    auto d = z - z;
    CHECK(d.isZero());
}

TEST_CASE("RatPoly: neg = scalar mul by -1") {
    auto x = RationalPolynomial::fromVar(VX, 1, 1);
    auto neg = -x;
    auto coeffs = neg.coefficients(VX);
    REQUIRE(coeffs.size() >= 2);
    CHECK(coeffs[1].constantValue() == -1);
}

TEST_CASE("RatPoly: pseudoRemainder of x² by (x - 1)") {
    // x² = (x-1)(x+1) + 1, so prem mod (x-1) gives a constant.
    RationalPolynomial p;
    p.addVar(VX, 2, 1);
    p.normalize();
    RationalPolynomial divisor;
    divisor.addVar(VX, 1, 1);
    divisor.addConstant(-1);
    divisor.normalize();
    auto r = p.pseudoRemainder(VX, divisor);
    // r should be lower-degree in x.
    CHECK(r.degree(VX) < divisor.degree(VX));
}
