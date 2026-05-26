// Univariate GCD over the tower field K = Q(alpha) (uses the exact tower inverse).
// Used by the exact root-membership oracle (G = gcd(F, beta's defining poly)).

#include <doctest/doctest.h>
#include <gmpxx.h>
#include "theory/arith/nra/valuation/TowerPolyGcd.h"

using namespace zolver;

static VarId A0 = VarId{100}, T = VarId{1};

static TowerContext emptyCtx() { return TowerContext{}; }   // K = Q
static TowerContext sqrt2Ctx() {
    TowerContext ctx;
    ctx.extensionVars = {A0};
    RationalPolynomial m0; m0.addVar(A0, 2, 1); m0.addConstant(-2); m0.normalize();
    ctx.minimalPolys = {m0};
    return ctx;
}

static RationalPolynomial monic(RationalPolynomial p) {
    p.normalize();
    if (p.isZero()) return p;
    mpq_class lead = p.terms().rbegin()->second;
    if (lead != 0 && lead != 1) { p *= (mpq_class(1) / lead); p.normalize(); }
    return p;
}
static bool sameUpToUnit(const RationalPolynomial& a, const RationalPolynomial& b) {
    return monic(a).terms() == monic(b).terms();
}

TEST_CASE("Tower gcd over Q: gcd(t^2-1, t-1) = t-1") {
    TowerKernel K(emptyCtx());
    RationalPolynomial f; f.addVar(T, 2, 1); f.addConstant(-1); f.normalize();
    RationalPolynomial g; g.addVar(T, 1, 1); g.addConstant(-1); g.normalize();
    auto r = towerPolyGcd(f, g, T, K);
    REQUIRE(r.ok);
    RationalPolynomial e; e.addVar(T, 1, 1); e.addConstant(-1); e.normalize();
    CHECK(sameUpToUnit(r.gcd, e));
}

TEST_CASE("Tower gcd over Q(sqrt2): gcd(t^2-2, t-alpha) = t-alpha") {
    TowerKernel K(sqrt2Ctx());
    RationalPolynomial f; f.addVar(T, 2, 1); f.addConstant(-2); f.normalize();      // t^2-2
    RationalPolynomial g; g.addVar(T, 1, 1); g.addVar(A0, 1, -1); g.normalize();    // t-A0
    auto r = towerPolyGcd(f, g, T, K);
    REQUIRE(r.ok);
    RationalPolynomial e; e.addVar(T, 1, 1); e.addVar(A0, 1, -1); e.normalize();    // t-A0
    CHECK(sameUpToUnit(r.gcd, e));
}

TEST_CASE("Tower gcd over Q(sqrt2): gcd(t-alpha, t+alpha) = 1 (coprime)") {
    TowerKernel K(sqrt2Ctx());
    RationalPolynomial f; f.addVar(T, 1, 1); f.addVar(A0, 1, -1); f.normalize();    // t-A0
    RationalPolynomial g; g.addVar(T, 1, 1); g.addVar(A0, 1, 1); g.normalize();     // t+A0
    auto r = towerPolyGcd(f, g, T, K);
    REQUIRE(r.ok);
    CHECK(r.gcd.isConstant());                  // gcd is a unit
}

TEST_CASE("Tower gcd over Q(sqrt2): gcd(t^2-2, t^2-2) = t^2-2") {
    TowerKernel K(sqrt2Ctx());
    RationalPolynomial f; f.addVar(T, 2, 1); f.addConstant(-2); f.normalize();
    auto r = towerPolyGcd(f, f, T, K);
    REQUIRE(r.ok);
    CHECK(sameUpToUnit(r.gcd, f));
}

TEST_CASE("Tower gcd over Q(sqrt2): gcd(t^2-3, t-alpha) = 1 (alpha not a root of t^2-3)") {
    TowerKernel K(sqrt2Ctx());
    RationalPolynomial f; f.addVar(T, 2, 1); f.addConstant(-3); f.normalize();      // t^2-3
    RationalPolynomial g; g.addVar(T, 1, 1); g.addVar(A0, 1, -1); g.normalize();    // t-A0 (=t-sqrt2)
    auto r = towerPolyGcd(f, g, T, K);
    REQUIRE(r.ok);
    CHECK(r.gcd.isConstant());
}
