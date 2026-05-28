// White-box: principal subresultant coefficient (PSC) chain — the algebraic
// core of the unconditionally-sound (Collins) NRA projection operator.
//
// Correctness anchors: psc_0 must equal the existing Sylvester `resultant`
// exactly (same matrix); psc_0 of (f, f') must reproduce the discriminant;
// the chain length must be min(deg_v p, deg_v q).

#include <doctest/doctest.h>
#include <gmpxx.h>
#include "theory/arith/nra/projection/SubresultantChain.h"
#include "theory/arith/nra/projection/LocalProjection.h"   // resultant()

using namespace xolver;

static VarId VX = VarId{1}, VY = VarId{2};

static bool sameConst(const RationalPolynomial& p, const mpq_class& c) {
    RationalPolynomial q = p;
    q.normalize();
    return q.isConstant() && q.constantValue() == c;
}

TEST_CASE("PSC: psc_0 of two linear polys equals their resultant") {
    RationalPolynomial f; f.addVar(VX, 1, 1); f.addConstant(-1); f.normalize();
    RationalPolynomial g; g.addVar(VX, 1, 1); g.addConstant(-2); g.normalize();

    auto r = principalSubresultantCoefficients(f, g, VX);
    CHECK_FALSE(r.budgetExceeded);
    REQUIRE(r.psc.size() == 1);
    CHECK(sameConst(r.psc[0], mpq_class(-1)));

    RationalPolynomial res = resultant(f, g, VX);
    res.normalize();
    CHECK(r.psc[0].terms() == res.terms());
}

TEST_CASE("PSC: psc_0 of (f, f') reproduces the discriminant (quadratic)") {
    RationalPolynomial f; f.addVar(VX, 2, 1); f.addVar(VX, 1, 3); f.addConstant(2);
    f.normalize();
    RationalPolynomial fp = f.derivative(VX);   // 2x + 3

    auto r = principalSubresultantCoefficients(f, fp, VX);
    CHECK_FALSE(r.budgetExceeded);
    REQUIRE(r.psc.size() == 1);
    CHECK(sameConst(r.psc[0], mpq_class(-1)));
}

TEST_CASE("PSC: discriminant of y^2 - x w.r.t. y is multiple of x") {
    RationalPolynomial f; f.addVar(VY, 2, 1); f.addVar(VX, 1, -1); f.normalize();
    RationalPolynomial fp = f.derivative(VY);   // 2y

    auto r = principalSubresultantCoefficients(f, fp, VY);
    CHECK_FALSE(r.budgetExceeded);
    REQUIRE(r.psc.size() == 1);
    RationalPolynomial e = r.psc[0]; e.normalize();
    CHECK(e.degree(VX) == 1);
    CHECK_FALSE(e.contains(VY));
    auto cs = e.coefficients(VX);
    REQUIRE(cs.size() == 2);
    CHECK(sameConst(cs[1], mpq_class(-4)));

    RationalPolynomial res = resultant(f, fp, VY); res.normalize();
    CHECK(r.psc[0].terms() == res.terms());
}

TEST_CASE("PSC: chain length is min(deg_v p, deg_v q)") {
    RationalPolynomial f;
    f.addVar(VX, 3, 1); f.addVar(VX, 1, 2); f.addConstant(-1); f.normalize();
    RationalPolynomial g;
    g.addVar(VX, 3, 2); g.addVar(VX, 2, 1); g.addConstant(5); g.normalize();

    auto r = principalSubresultantCoefficients(f, g, VX);
    CHECK_FALSE(r.budgetExceeded);
    CHECK(r.psc.size() == 3);
    RationalPolynomial res = resultant(f, g, VX); res.normalize();
    RationalPolynomial p0 = r.psc[0]; p0.normalize();
    CHECK(p0.terms() == res.terms());
}

TEST_CASE("PSC: degree < 1 in v gives empty chain") {
    RationalPolynomial cst = RationalPolynomial::fromConstant(mpq_class(5));
    RationalPolynomial f; f.addVar(VX, 2, 1); f.normalize();
    auto r = principalSubresultantCoefficients(f, cst, VX);
    CHECK(r.psc.empty());
    CHECK_FALSE(r.budgetExceeded);
}

TEST_CASE("PSC: size budget trips budgetExceeded, never throws") {
    RationalPolynomial f; f.addVar(VX, 6, 1); f.addConstant(-1); f.normalize();
    RationalPolynomial g; g.addVar(VX, 6, 1); g.addConstant(1);  g.normalize();
    auto r = principalSubresultantCoefficients(f, g, VX, /*maxMatrixDim=*/4);
    CHECK(r.budgetExceeded);
}
