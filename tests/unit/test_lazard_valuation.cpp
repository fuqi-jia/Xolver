// Step C [H3]: Lazard valuation — evaluate a polynomial at a tower prefix to a
// univariate in the lift variable, recovering nullification via derivative order.

#include <doctest/doctest.h>
#include <gmpxx.h>
#include "theory/arith/logics/nra/valuation/LazardValuationEngine.h"

using namespace xolver;

static VarId A0 = VarId{100}, Y = VarId{2};

// Prefix coordinate A0 = c (rational): minimal poly A0 - c (monic, degree 1).
static TowerContext rationalCtx(const mpq_class& c) {
    TowerContext ctx;
    ctx.extensionVars = {A0};
    RationalPolynomial m; m.addVar(A0, 1, 1); m.addConstant(-c); m.normalize();
    ctx.minimalPolys = {m};
    return ctx;
}
// Prefix coordinate A0 = sqrt2: minimal poly A0^2 - 2.
static TowerContext sqrt2Ctx() {
    TowerContext ctx;
    ctx.extensionVars = {A0};
    RationalPolynomial m; m.addVar(A0, 2, 1); m.addConstant(-2); m.normalize();
    ctx.minimalPolys = {m};
    return ctx;
}

TEST_CASE("Valuation: (y^2 - x) at x=2 => y^2 - 2, multiplicity 0 (ordinary)") {
    RationalPolynomial p; p.addVar(Y, 2, 1); p.addVar(A0, 1, -1); p.normalize();  // y^2 - A0
    auto r = lazardEvaluateToUnivariate(p, Y, rationalCtx(2));
    REQUIRE(r.complete());
    REQUIRE(r.trace.size() == 1);
    CHECK(r.trace[0].multiplicity == 0);
    RationalPolynomial e; e.addVar(Y, 2, 1); e.addConstant(-2); e.normalize();
    CHECK(r.univariate.terms() == e.terms());
}

TEST_CASE("Valuation: x*(y+1) at x=0 nullifies; recovers y+1, multiplicity 1") {
    RationalPolynomial p; p.addTerm({{A0, 1}, {Y, 1}}, 1); p.addVar(A0, 1, 1); p.normalize();  // A0*y + A0
    auto r = lazardEvaluateToUnivariate(p, Y, rationalCtx(0));
    REQUIRE(r.complete());
    CHECK(r.trace[0].multiplicity == 1);
    RationalPolynomial e; e.addVar(Y, 1, 1); e.addConstant(1); e.normalize();  // y+1
    CHECK(r.univariate.terms() == e.terms());
}

TEST_CASE("Valuation: x^2*(y^2-2) at x=0 nullifies twice; recovers 2(y^2-2), multiplicity 2") {
    // A0^2 * (y^2 - 2) = A0^2 y^2 - 2 A0^2
    RationalPolynomial p; p.addTerm({{A0, 2}, {Y, 2}}, 1); p.addVar(A0, 2, -2); p.normalize();
    auto r = lazardEvaluateToUnivariate(p, Y, rationalCtx(0));
    REQUIRE(r.complete());
    CHECK(r.trace[0].multiplicity == 2);
    RationalPolynomial e; e.addVar(Y, 2, 2); e.addConstant(-4); e.normalize();  // 2y^2 - 4
    CHECK(r.univariate.terms() == e.terms());
}

TEST_CASE("Valuation: (x^2-2)(y-1) at x=sqrt2 nullifies; recovers 2*A0*(y-1), multiplicity 1") {
    // (A0^2 - 2)(y - 1) = A0^2 y - A0^2 - 2y + 2
    RationalPolynomial p;
    p.addTerm({{A0, 2}, {Y, 1}}, 1);
    p.addVar(A0, 2, -1);
    p.addVar(Y, 1, -2);
    p.addConstant(2);
    p.normalize();
    auto r = lazardEvaluateToUnivariate(p, Y, sqrt2Ctx());
    REQUIRE(r.complete());
    CHECK(r.trace[0].multiplicity == 1);
    // residual = d/dA0 [(A0^2-2)(y-1)] = 2 A0 (y-1) = 2 A0 y - 2 A0
    RationalPolynomial e;
    e.addTerm({{A0, 1}, {Y, 1}}, 2);
    e.addVar(A0, 1, -2);
    e.normalize();
    CHECK(r.univariate.terms() == e.terms());
}

TEST_CASE("Valuation: polynomial independent of the prefix var is returned unchanged") {
    RationalPolynomial p; p.addVar(Y, 2, 1); p.addConstant(-3); p.normalize();  // y^2 - 3
    auto r = lazardEvaluateToUnivariate(p, Y, sqrt2Ctx());
    REQUIRE(r.complete());
    CHECK(r.trace[0].multiplicity == 0);
    CHECK(r.univariate.terms() == p.terms());
}
