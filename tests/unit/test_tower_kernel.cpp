// Step B.1: exact arithmetic + zero-test in the algebraic-coefficient tower
// Q(alpha_0,...) ~= Q[A]/<m_i> (LAZARD.md [H1]). All exact; no root isolation.

#include <doctest/doctest.h>
#include <gmpxx.h>
#include "theory/arith/nra/valuation/TowerAlgebraicKernel.h"

using namespace nlcolver;

static VarId A0 = VarId{100}, A1 = VarId{101};

// ctx for Q(sqrt 2): m0 = A0^2 - 2 (monic in A0).
static TowerContext sqrt2Ctx() {
    TowerContext ctx;
    ctx.extensionVars = {A0};
    RationalPolynomial m0; m0.addVar(A0, 2, 1); m0.addConstant(-2); m0.normalize();
    ctx.minimalPolys = {m0};
    return ctx;
}

// ctx for Q(sqrt 2, sqrt sqrt 2): m0 = A0^2-2, m1 = A1^2 - A0 (monic in A1).
static TowerContext quadTowerCtx() {
    TowerContext ctx;
    ctx.extensionVars = {A0, A1};
    RationalPolynomial m0; m0.addVar(A0, 2, 1); m0.addConstant(-2); m0.normalize();
    RationalPolynomial m1; m1.addVar(A1, 2, 1); m1.addVar(A0, 1, -1); m1.normalize();
    ctx.minimalPolys = {m0, m1};
    return ctx;
}

TEST_CASE("Tower Q(sqrt2): alpha^2 == 2") {
    TowerKernel K(sqrt2Ctx());
    auto a = K.generator(0);
    CHECK(K.equal(K.mul(a, a), K.fromRational(2)));
    CHECK_FALSE(K.equal(K.mul(a, a), K.fromRational(3)));
}

TEST_CASE("Tower Q(sqrt2): (alpha-1)(alpha+1) == 1") {
    TowerKernel K(sqrt2Ctx());
    auto a = K.generator(0);
    auto one = K.fromRational(1);
    auto lhs = K.mul(K.sub(a, one), K.add(a, one));   // alpha^2 - 1 = 2 - 1
    CHECK(K.equal(lhs, one));
}

TEST_CASE("Tower Q(sqrt2): exact zero-test of A0^2 - 2") {
    TowerKernel K(sqrt2Ctx());
    RationalPolynomial p; p.addVar(A0, 2, 1); p.addConstant(-2); p.normalize();
    CHECK(K.reduce(p).isZero());
    RationalPolynomial q; q.addVar(A0, 2, 1); q.addConstant(-3); q.normalize();
    CHECK_FALSE(K.reduce(q).isZero());   // reduces to -1
}

TEST_CASE("Tower Q(sqrt2): rational arithmetic exact") {
    TowerKernel K(sqrt2Ctx());
    auto s = K.add(K.fromRational(mpq_class(1, 2)), K.fromRational(mpq_class(1, 3)));
    CHECK(K.equal(s, K.fromRational(mpq_class(5, 6))));
}

TEST_CASE("Tower Q(sqrt2, sqrt sqrt2): beta^2 == alpha and beta^4 == 2") {
    TowerKernel K(quadTowerCtx());
    auto alpha = K.generator(0);   // sqrt 2
    auto beta = K.generator(1);    // sqrt sqrt 2
    auto beta2 = K.mul(beta, beta);
    CHECK(K.equal(beta2, alpha));               // beta^2 = alpha
    auto beta4 = K.mul(beta2, beta2);
    CHECK(K.equal(beta4, K.fromRational(2)));    // beta^4 = 2
    CHECK_FALSE(K.equal(beta4, K.fromRational(4)));
}

TEST_CASE("Tower Q(sqrt2, sqrt sqrt2): mixed reduction (alpha*beta)^2 == 2*alpha") {
    TowerKernel K(quadTowerCtx());
    auto alpha = K.generator(0);
    auto beta = K.generator(1);
    auto ab = K.mul(alpha, beta);
    auto ab2 = K.mul(ab, ab);                    // alpha^2 * beta^2 = 2 * alpha
    CHECK(K.equal(ab2, K.mul(K.fromRational(2), alpha)));
}

TEST_CASE("Tower: degree-1 minimal poly reduces generator to a constant") {
    // m0 = A0 - 5  =>  alpha_0 == 5.
    TowerContext ctx;
    ctx.extensionVars = {A0};
    RationalPolynomial m0; m0.addVar(A0, 1, 1); m0.addConstant(-5); m0.normalize();
    ctx.minimalPolys = {m0};
    TowerKernel K(ctx);
    CHECK(K.equal(K.generator(0), K.fromRational(5)));
}
