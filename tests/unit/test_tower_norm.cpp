// Step B.2.a: Norm candidate generation over a tower (LAZARD.md [H2] stage 1).
// Norm_Q(F) eliminates every extension variable against its minimal poly,
// yielding a univariate over Q whose roots are a SUPERSET of the true roots.

#include <doctest/doctest.h>
#include <gmpxx.h>
#include "theory/arith/nra/valuation/TowerRootIsolation.h"

using namespace xolver;

static VarId A0 = VarId{100}, A1 = VarId{101}, X = VarId{1};

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

static TowerContext sqrt2Ctx() {
    TowerContext ctx;
    ctx.extensionVars = {A0};
    RationalPolynomial m0; m0.addVar(A0, 2, 1); m0.addConstant(-2); m0.normalize();
    ctx.minimalPolys = {m0};
    return ctx;
}
static TowerContext quadTowerCtx() {
    TowerContext ctx;
    ctx.extensionVars = {A0, A1};
    RationalPolynomial m0; m0.addVar(A0, 2, 1); m0.addConstant(-2); m0.normalize();
    RationalPolynomial m1; m1.addVar(A1, 2, 1); m1.addVar(A0, 1, -1); m1.normalize();
    ctx.minimalPolys = {m0, m1};
    return ctx;
}

TEST_CASE("Tower Norm: F = x - sqrt2  =>  N = x^2 - 2") {
    // F = x - A0
    RationalPolynomial F; F.addVar(X, 1, 1); F.addVar(A0, 1, -1); F.normalize();
    auto r = towerNorm(F, X, sqrt2Ctx());
    REQUIRE(r.ok);
    RationalPolynomial expect; expect.addVar(X, 2, 1); expect.addConstant(-2); expect.normalize();
    CHECK(sameUpToUnit(r.norm, expect));
}

TEST_CASE("Tower Norm: F = x^2 - sqrt2  =>  N = x^4 - 2") {
    RationalPolynomial F; F.addVar(X, 2, 1); F.addVar(A0, 1, -1); F.normalize();
    auto r = towerNorm(F, X, sqrt2Ctx());
    REQUIRE(r.ok);
    RationalPolynomial expect; expect.addVar(X, 4, 1); expect.addConstant(-2); expect.normalize();
    CHECK(sameUpToUnit(r.norm, expect));
}

TEST_CASE("Tower Norm: two-generator F = x - sqrt(sqrt2)  =>  N = x^4 - 2") {
    // F = x - A1, A1 = sqrt(sqrt 2); eliminating A1 then A0 gives x^4 - 2.
    RationalPolynomial F; F.addVar(X, 1, 1); F.addVar(A1, 1, -1); F.normalize();
    auto r = towerNorm(F, X, quadTowerCtx());
    REQUIRE(r.ok);
    RationalPolynomial expect; expect.addVar(X, 4, 1); expect.addConstant(-2); expect.normalize();
    CHECK(sameUpToUnit(r.norm, expect));
}

TEST_CASE("Tower Norm: result is over Q (no extension variables remain)") {
    RationalPolynomial F; F.addVar(X, 1, 1); F.addVar(A0, 1, -1); F.normalize();
    auto r = towerNorm(F, X, sqrt2Ctx());
    REQUIRE(r.ok);
    CHECK_FALSE(r.norm.contains(A0));
    CHECK(r.norm.contains(X));
}

TEST_CASE("Tower Norm: F = x - (sqrt2 + 1) => N = x^2 - 2x - 1 (min poly of 1+sqrt2)") {
    // F = x - A0 - 1
    RationalPolynomial F; F.addVar(X, 1, 1); F.addVar(A0, 1, -1); F.addConstant(-1); F.normalize();
    auto r = towerNorm(F, X, sqrt2Ctx());
    REQUIRE(r.ok);
    // (x-1-sqrt2)(x-1+sqrt2) = (x-1)^2 - 2 = x^2 - 2x - 1
    RationalPolynomial expect; expect.addVar(X, 2, 1); expect.addVar(X, 1, -2); expect.addConstant(-1);
    expect.normalize();
    CHECK(sameUpToUnit(r.norm, expect));
}

TEST_CASE("Tower root isolation [H2] is unsupported until the exact filter lands") {
    RationalPolynomial F; F.addVar(X, 1, 1); F.addVar(A0, 1, -1); F.normalize();
    auto r = isolateRealRootsInTower(F, X, sqrt2Ctx());
    CHECK_FALSE(r.supported);   // sound: caller => Unknown
}
