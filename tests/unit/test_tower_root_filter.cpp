// Step 3: interval fast-filter in isolateRealRootsInTower. Soundly proves
// "F has NO real roots at the embedding" (dropping conjugate/extraneous Norm
// roots), else reports unsupported (=> caller Unknown; exact placement is step 4).

#include <doctest/doctest.h>
#include <gmpxx.h>
#include "theory/arith/nra/valuation/TowerRootIsolation.h"

using namespace nlcolver;

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

TEST_CASE("Filter k=0: x^2+1 has no real roots => supported, empty") {
    RationalPolynomial F; F.addVar(X, 2, 1); F.addConstant(1); F.normalize();
    auto r = isolateRealRootsInTower(F, X, TowerContext{});
    CHECK(r.supported);
    CHECK(r.roots.empty());
}

TEST_CASE("Filter k=0: x^2-2 has real roots => unsupported (deferred to step 4)") {
    RationalPolynomial F; F.addVar(X, 2, 1); F.addConstant(-2); F.normalize();
    auto r = isolateRealRootsInTower(F, X, TowerContext{});
    CHECK_FALSE(r.supported);
}

TEST_CASE("Filter: x^2 + sqrt2 has NO real roots; Norm x^4-2 conjugate roots dropped") {
    // F = X^2 + A0; at alpha=+sqrt2 this is X^2+sqrt2 > 0 (no real root). The Norm
    // x^4-2 has real roots +-2^{1/4} (the conjugate alpha=-sqrt2 branch), which the
    // interval filter must DROP.
    RationalPolynomial F; F.addVar(X, 2, 1); F.addVar(A0, 1, 1); F.normalize();
    auto r = isolateRealRootsInTower(F, X, sqrt2Ctx());
    CHECK(r.supported);
    CHECK(r.roots.empty());
}

TEST_CASE("Filter: x^2 - sqrt2 HAS real roots (+-2^{1/4}) => unsupported") {
    // F = X^2 - A0; at alpha=+sqrt2 this is X^2-sqrt2 = 0 => X = +-2^{1/4} (real).
    RationalPolynomial F; F.addVar(X, 2, 1); F.addVar(A0, 1, -1); F.normalize();
    auto r = isolateRealRootsInTower(F, X, sqrt2Ctx());
    CHECK_FALSE(r.supported);
}

TEST_CASE("Filter: x^2 + 1 over Q(sqrt2) (no generator dependence) => no real roots") {
    RationalPolynomial F; F.addVar(X, 2, 1); F.addConstant(1); F.normalize();
    auto r = isolateRealRootsInTower(F, X, sqrt2Ctx());
    CHECK(r.supported);
    CHECK(r.roots.empty());
}

TEST_CASE("Filter: (x^2+sqrt2)+1 strictly positive => no real roots") {
    // X^2 + A0 + 1; at alpha=sqrt2 ~ 2.414 + X^2 > 0.
    RationalPolynomial F; F.addVar(X, 2, 1); F.addVar(A0, 1, 1); F.addConstant(1); F.normalize();
    auto r = isolateRealRootsInTower(F, X, sqrt2Ctx());
    CHECK(r.supported);
    CHECK(r.roots.empty());
}
