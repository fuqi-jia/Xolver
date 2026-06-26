// Stress / soundness suite for the completed Lazard primitives:
//   - tower field axioms (assoc, distrib, inverse round-trip) over Q(sqrt2)
//     and the two-generator towers Q(sqrt2, sqrt sqrt2), Q(sqrt2, sqrt3);
//   - Norm == minimal polynomial cross-checks (degree-correct);
//   - projection-closure geometric boundary cross-checks (circle/ellipse);
//   - squarefree on products with repeated factors.
// All exact; no root isolation.

#include <doctest/doctest.h>
#include <gmpxx.h>
#include "theory/arith/logics/nra/valuation/TowerAlgebraicKernel.h"
#include "theory/arith/logics/nra/valuation/TowerRootIsolation.h"
#include "theory/arith/logics/nra/projection/LazardProjectionClosure.h"
#include "theory/arith/logics/nra/projection/Squarefree.h"

using namespace xolver;

static VarId A0 = VarId{100}, A1 = VarId{101}, X = VarId{1}, Y = VarId{2};

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
static TowerContext quadTowerCtx() {  // Q(sqrt2, sqrt sqrt2)
    TowerContext ctx;
    ctx.extensionVars = {A0, A1};
    RationalPolynomial m0; m0.addVar(A0, 2, 1); m0.addConstant(-2); m0.normalize();
    RationalPolynomial m1; m1.addVar(A1, 2, 1); m1.addVar(A0, 1, -1); m1.normalize();
    ctx.minimalPolys = {m0, m1};
    return ctx;
}
static TowerContext sqrt2sqrt3Ctx() {  // Q(sqrt2, sqrt3)
    TowerContext ctx;
    ctx.extensionVars = {A0, A1};
    RationalPolynomial m0; m0.addVar(A0, 2, 1); m0.addConstant(-2); m0.normalize();
    RationalPolynomial m1; m1.addVar(A1, 2, 1); m1.addConstant(-3); m1.normalize();
    ctx.minimalPolys = {m0, m1};
    return ctx;
}

// ---- Tower field axioms over a coefficient grid ---------------------------

TEST_CASE("Stress: Q(sqrt2) field axioms over a coefficient grid") {
    TowerKernel K(sqrt2Ctx());
    auto a = K.generator(0);
    for (int p = -3; p <= 3; ++p)
    for (int q = -3; q <= 3; ++q) {
        // e = p + q*alpha
        TowerElement e = K.add(K.fromRational(p), K.mul(K.fromRational(q), a));
        for (int r = -3; r <= 3; ++r)
        for (int s = -2; s <= 2; ++s) {
            TowerElement f = K.add(K.fromRational(r), K.mul(K.fromRational(s), a));
            // distributivity: a*(e+f) == a*e + a*f
            CHECK(K.equal(K.mul(a, K.add(e, f)),
                          K.add(K.mul(a, e), K.mul(a, f))));
            // commutativity of *
            CHECK(K.equal(K.mul(e, f), K.mul(f, e)));
        }
        // inverse round-trip for nonzero e (e = p + q*sqrt2 == 0 only if p=q=0)
        if (!(p == 0 && q == 0)) {
            auto inv = K.inverse(e);
            REQUIRE(inv.has_value());
            CHECK(K.equal(K.mul(e, *inv), K.fromRational(1)));
        }
    }
}

TEST_CASE("Stress: Q(sqrt2, sqrt3) inverse round-trip over a grid") {
    TowerKernel K(sqrt2sqrt3Ctx());
    auto a = K.generator(0), b = K.generator(1);   // sqrt2, sqrt3
    for (int p = -2; p <= 2; ++p)
    for (int q = -2; q <= 2; ++q)
    for (int r = -2; r <= 2; ++r) {
        if (p == 0 && q == 0 && r == 0) continue;
        // e = p + q*sqrt2 + r*sqrt3  (nonzero: 1, sqrt2, sqrt3 are Q-independent)
        TowerElement e = K.add(K.add(K.fromRational(p), K.mul(K.fromRational(q), a)),
                               K.mul(K.fromRational(r), b));
        auto inv = K.inverse(e);
        REQUIRE(inv.has_value());
        CHECK(K.equal(K.mul(e, *inv), K.fromRational(1)));
    }
}

// ---- Norm == minimal polynomial -------------------------------------------

TEST_CASE("Stress: Norm(x - element) == minimal polynomial") {
    // sqrt2 -> x^2 - 2
    {
        TowerKernel K(sqrt2Ctx());
        RationalPolynomial F; F.addVar(X, 1, 1); F.addVar(A0, 1, -1); F.normalize();  // x - A0
        auto r = towerNorm(F, X, sqrt2Ctx()); REQUIRE(r.ok);
        RationalPolynomial e; e.addVar(X, 2, 1); e.addConstant(-2); e.normalize();
        CHECK(sameUpToUnit(r.norm, e));
    }
    // 1 + sqrt2 -> x^2 - 2x - 1
    {
        RationalPolynomial F; F.addVar(X, 1, 1); F.addVar(A0, 1, -1); F.addConstant(-1); F.normalize();
        auto r = towerNorm(F, X, sqrt2Ctx()); REQUIRE(r.ok);
        RationalPolynomial e; e.addVar(X, 2, 1); e.addVar(X, 1, -2); e.addConstant(-1); e.normalize();
        CHECK(sameUpToUnit(r.norm, e));
    }
    // sqrt(sqrt2) -> x^4 - 2
    {
        RationalPolynomial F; F.addVar(X, 1, 1); F.addVar(A1, 1, -1); F.normalize();  // x - A1
        auto r = towerNorm(F, X, quadTowerCtx()); REQUIRE(r.ok);
        RationalPolynomial e; e.addVar(X, 4, 1); e.addConstant(-2); e.normalize();
        CHECK(sameUpToUnit(r.norm, e));
    }
    // sqrt2 + sqrt3 -> x^4 - 10x^2 + 1  (degree 4 = [Q(sqrt2,sqrt3):Q])
    {
        RationalPolynomial F; F.addVar(X, 1, 1); F.addVar(A0, 1, -1); F.addVar(A1, 1, -1); F.normalize();
        auto r = towerNorm(F, X, sqrt2sqrt3Ctx()); REQUIRE(r.ok);
        RationalPolynomial e; e.addVar(X, 4, 1); e.addVar(X, 2, -10); e.addConstant(1); e.normalize();
        CHECK(sameUpToUnit(r.norm, e));
    }
}

// ---- Projection geometric boundary cross-checks ---------------------------

TEST_CASE("Stress: closure of unit circle x^2+y^2-1 over [x,y] => x-boundary x^2-1") {
    RationalPolynomial p; p.addVar(X, 2, 1); p.addVar(Y, 2, 1); p.addConstant(-1); p.normalize();
    LazardProjectionClosure cl;
    auto reason = cl.build({p}, {X, Y});
    CHECK(reason == LazardIncompleteReason::None);
    REQUIRE(cl.levelPolys(0).size() == 1);
    RationalPolynomial e; e.addVar(X, 2, 1); e.addConstant(-1); e.normalize();   // x^2-1 (roots +-1)
    CHECK(sameUpToUnit(cl.entries()[cl.levelPolys(0)[0]].poly, e));
}

TEST_CASE("Stress: closure of ellipse 4x^2+y^2-4 over [x,y] => x-boundary x^2-1") {
    RationalPolynomial p; p.addVar(X, 2, 4); p.addVar(Y, 2, 1); p.addConstant(-4); p.normalize();
    LazardProjectionClosure cl;
    auto reason = cl.build({p}, {X, Y});
    CHECK(reason == LazardIncompleteReason::None);
    REQUIRE(cl.levelPolys(0).size() == 1);
    RationalPolynomial e; e.addVar(X, 2, 1); e.addConstant(-1); e.normalize();   // x in [-1,1]
    CHECK(sameUpToUnit(cl.entries()[cl.levelPolys(0)[0]].poly, e));
}

// ---- Squarefree on repeated-factor products -------------------------------

TEST_CASE("Stress: squarefreePart_x((x-1)^2 (x-2)^3) == (x-1)(x-2)") {
    // (x-1)^2 = x^2-2x+1 ; (x-2)^3 = x^3-6x^2+12x-8 ; product expanded below.
    RationalPolynomial a; a.addVar(X, 2, 1); a.addVar(X, 1, -2); a.addConstant(1); a.normalize();
    RationalPolynomial b; b.addVar(X, 3, 1); b.addVar(X, 2, -6); b.addVar(X, 1, 12); b.addConstant(-8);
    b.normalize();
    RationalPolynomial p = a * b; p.normalize();
    auto s = squarefreePartWrt(p, X);
    CHECK(s.complete);
    // (x-1)(x-2) = x^2 - 3x + 2
    RationalPolynomial e; e.addVar(X, 2, 1); e.addVar(X, 1, -3); e.addConstant(2); e.normalize();
    CHECK(sameUpToUnit(s.poly, e));
}

TEST_CASE("Stress: squarefreePart_x(x^2*(x^2-2)) == x*(x^2-2)") {
    RationalPolynomial p; p.addVar(X, 4, 1); p.addVar(X, 2, -2); p.normalize();  // x^4 - 2x^2
    auto s = squarefreePartWrt(p, X);
    CHECK(s.complete);
    RationalPolynomial e; e.addVar(X, 3, 1); e.addVar(X, 1, -2); e.normalize();  // x^3 - 2x
    CHECK(sameUpToUnit(s.poly, e));
}
