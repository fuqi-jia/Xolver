// Step A [H4]: multivariate content / primitivePart / squarefreePart w.r.t. a
// variable — the primitive squarefree basis the Lazard projection operator
// consumes. Comparisons are up-to-rational-unit (monic in the largest monomial).

#include <doctest/doctest.h>
#include <gmpxx.h>
#include "search/nra/lazard/Squarefree.h"

using namespace xolver;

TEST_CASE("contentWrt: a nonzero rational coefficient resolves symbolic content before gcd") {
    const VarId a = 1, b = 2, x = 3;
    for (const mpq_class unit : {mpq_class(1), mpq_class(7, 3), mpq_class(-3, 7)}) {
        RationalPolynomial p;
        p.addTerm({{a, 1}, {b, 1}}, 1);
        p.addTerm({{a, 1}, {x, 1}}, -1);
        p.addTerm({{b, 1}, {x, 1}}, -1);
        p.addVar(x, 2, unit);
        p.normalize();
        const auto content = contentWrt(p, x);
        REQUIRE(content.complete);
        REQUIRE(content.poly.isConstant());
        CHECK(content.poly.constantValue() == 1);
    }
}

static VarId VX = VarId{1}, VY = VarId{2};

static RationalPolynomial monic(const RationalPolynomial& p) {
    RationalPolynomial q = p;
    q.normalize();
    if (q.isZero()) return q;
    mpq_class lead = q.terms().rbegin()->second;
    if (lead != 0 && lead != 1) { q *= (mpq_class(1) / lead); q.normalize(); }
    return q;
}
static bool sameUpToUnit(const RationalPolynomial& a, const RationalPolynomial& b) {
    return monic(a).terms() == monic(b).terms();
}

TEST_CASE("Squarefree: content_x(y*x + y) = y") {
    RationalPolynomial p;
    p.addTerm({{VX, 1}, {VY, 1}}, 1);   // x*y
    p.addTerm({{VY, 1}}, 1);            // y
    p.normalize();
    auto c = contentWrt(p, VX);
    CHECK(c.complete);
    RationalPolynomial y; y.addVar(VY, 1, 1); y.normalize();
    CHECK(sameUpToUnit(c.poly, y));
}

TEST_CASE("Squarefree: primitivePart_x(y*x + y) = x + 1") {
    RationalPolynomial p;
    p.addTerm({{VX, 1}, {VY, 1}}, 1);
    p.addTerm({{VY, 1}}, 1);
    p.normalize();
    auto pp = primitivePartWrt(p, VX);
    CHECK(pp.complete);
    RationalPolynomial xp1; xp1.addVar(VX, 1, 1); xp1.addConstant(1); xp1.normalize();
    CHECK(sameUpToUnit(pp.poly, xp1));
}

TEST_CASE("Squarefree: squarefreePart_x((x-y)^2) = x - y") {
    // (x-y)^2 = x^2 - 2xy + y^2
    RationalPolynomial p;
    p.addVar(VX, 2, 1);
    p.addTerm({{VX, 1}, {VY, 1}}, -2);
    p.addVar(VY, 2, 1);
    p.normalize();
    auto s = squarefreePartWrt(p, VX);
    CHECK(s.complete);
    RationalPolynomial xy; xy.addVar(VX, 1, 1); xy.addVar(VY, 1, -1); xy.normalize();
    CHECK(sameUpToUnit(s.poly, xy));
}

TEST_CASE("Squarefree: squarefreePart_x(y*(x+1)^2) = x + 1") {
    // y*(x+1)^2 = y*x^2 + 2y*x + y
    RationalPolynomial p;
    p.addTerm({{VX, 2}, {VY, 1}}, 1);
    p.addTerm({{VX, 1}, {VY, 1}}, 2);
    p.addTerm({{VY, 1}}, 1);
    p.normalize();
    auto s = squarefreePartWrt(p, VX);
    CHECK(s.complete);
    RationalPolynomial xp1; xp1.addVar(VX, 1, 1); xp1.addConstant(1); xp1.normalize();
    CHECK(sameUpToUnit(s.poly, xp1));
}

TEST_CASE("Squarefree: x^2 - y^2 already squarefree w.r.t. x") {
    RationalPolynomial p;
    p.addVar(VX, 2, 1);
    p.addVar(VY, 2, -1);
    p.normalize();
    auto s = squarefreePartWrt(p, VX);
    CHECK(s.complete);
    CHECK(sameUpToUnit(s.poly, p));
}

TEST_CASE("Squarefree: univariate squarefree x^2 - 2 w.r.t. x unchanged") {
    RationalPolynomial p;
    p.addVar(VX, 2, 1);
    p.addConstant(-2);
    p.normalize();
    auto s = squarefreePartWrt(p, VX);
    CHECK(s.complete);
    CHECK(sameUpToUnit(s.poly, p));
}
