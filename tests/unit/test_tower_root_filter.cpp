// isolateRealRootsInTower: Norm candidates -> exact root-membership oracle.
// supported+roots when every candidate is decided (Keep placed / Drop discarded);
// supported+empty proves NO real roots (conjugates dropped); unsupported on any
// Unknown candidate (=> caller Unknown, never UNSAT).

#include <doctest/doctest.h>
#include <gmpxx.h>
#include "theory/arith/logics/nra/lazard/TowerRootIsolation.h"

using namespace xolver;

static VarId A0 = VarId{100}, X = VarId{1};

// Q(sqrt2) with the real embedding alpha in [7/5, 3/2] (contains 1.4142...).
static TowerContext sqrt2Ctx() {
    TowerContext ctx;
    ctx.extensionVars = {A0};
    RationalPolynomial m0; m0.addVar(A0, 2, 1); m0.addConstant(-2); m0.normalize();
    ctx.minimalPolys = {m0};
    AlgebraicRoot ar; ar.lower = mpq_class(7, 5); ar.upper = mpq_class(3, 2);
    ctx.generators = {RealAlg::fromAlgebraic(ar)};
    return ctx;
}

TEST_CASE("Isolate k=0: x^2+1 has no real roots => supported, empty") {
    RationalPolynomial F; F.addVar(X, 2, 1); F.addConstant(1); F.normalize();
    auto r = isolateRealRootsInTower(F, X, TowerContext{});
    CHECK(r.supported);
    CHECK(r.rootIntervals.empty());
}

TEST_CASE("Isolate k=0: x^2-2 places its two real roots (oracle keeps both)") {
    RationalPolynomial F; F.addVar(X, 2, 1); F.addConstant(-2); F.normalize();
    auto r = isolateRealRootsInTower(F, X, TowerContext{});
    CHECK(r.supported);
    CHECK(r.rootIntervals.size() == 2);
}

TEST_CASE("Isolate: x^2 + sqrt2 has NO real roots; Norm x^4-2 conjugate roots dropped") {
    // At alpha=+sqrt2, X^2+sqrt2 > 0. Norm x^4-2 has real roots +-2^{1/4} (the
    // alpha=-sqrt2 branch); the oracle must DROP both => empty.
    RationalPolynomial F; F.addVar(X, 2, 1); F.addVar(A0, 1, 1); F.normalize();
    auto r = isolateRealRootsInTower(F, X, sqrt2Ctx());
    CHECK(r.supported);
    CHECK(r.rootIntervals.empty());
}

TEST_CASE("Isolate: x^2 - sqrt2 => Unknown (degree-2 proper factor needs Trager)") {
    // F=X^2-A0 has real roots +-2^{1/4}; gcd_K(F, x^4-2) = X^2-A0 is a degree-2
    // proper factor (not linear, not full), so the oracle returns Unknown =>
    // isolation unsupported. Sound (never UNSAT); placement awaits Trager.
    RationalPolynomial F; F.addVar(X, 2, 1); F.addVar(A0, 1, -1); F.normalize();
    auto r = isolateRealRootsInTower(F, X, sqrt2Ctx());
    CHECK_FALSE(r.supported);
}

TEST_CASE("Isolate: t - alpha over Q(sqrt2) places the single root +sqrt2") {
    // F = X - A0; Norm = x^2-2, candidates +-sqrt2; oracle keeps +sqrt2, drops -sqrt2.
    RationalPolynomial F; F.addVar(X, 1, 1); F.addVar(A0, 1, -1); F.normalize();
    auto r = isolateRealRootsInTower(F, X, sqrt2Ctx());
    CHECK(r.supported);
    REQUIRE(r.rootIntervals.size() == 1);
    // the kept root is +sqrt2 (in (1,2), positive)
    CHECK(r.rootIntervals[0].second > mpq_class(0));
}

TEST_CASE("Isolate: x^2 + 1 over Q(sqrt2) => no real roots") {
    RationalPolynomial F; F.addVar(X, 2, 1); F.addConstant(1); F.normalize();
    auto r = isolateRealRootsInTower(F, X, sqrt2Ctx());
    CHECK(r.supported);
    CHECK(r.rootIntervals.empty());
}
