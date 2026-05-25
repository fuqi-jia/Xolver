// Step B.1.5: exact field inverse / division in the tower (recursive
// extended-Euclid mod each irreducible minimal poly). Needed by the B.2.b
// exact root filter (extend the tower with beta's min poly over Q(alpha)).

#include <doctest/doctest.h>
#include <gmpxx.h>
#include "theory/arith/nra/valuation/TowerAlgebraicKernel.h"

using namespace nlcolver;

static VarId A0 = VarId{100}, A1 = VarId{101};

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

TEST_CASE("Tower inverse Q(sqrt2): 1/alpha == alpha/2, and alpha * (1/alpha) == 1") {
    TowerKernel K(sqrt2Ctx());
    auto a = K.generator(0);
    auto ai = K.inverse(a);
    REQUIRE(ai.has_value());
    CHECK(K.equal(K.mul(a, *ai), K.fromRational(1)));
    // 1/sqrt2 = sqrt2 / 2 = (1/2)*alpha
    auto half_alpha = K.mul(K.fromRational(mpq_class(1, 2)), a);
    CHECK(K.equal(*ai, half_alpha));
}

TEST_CASE("Tower inverse Q(sqrt2): 1/(alpha+1) == alpha-1") {
    TowerKernel K(sqrt2Ctx());
    auto a = K.generator(0);
    auto ap1 = K.add(a, K.fromRational(1));
    auto inv = K.inverse(ap1);
    REQUIRE(inv.has_value());
    CHECK(K.equal(K.mul(ap1, *inv), K.fromRational(1)));
    auto am1 = K.sub(a, K.fromRational(1));   // sqrt2 - 1
    CHECK(K.equal(*inv, am1));
}

TEST_CASE("Tower inverse: rational 1/3, and div") {
    TowerKernel K(sqrt2Ctx());
    auto inv3 = K.inverse(K.fromRational(3));
    REQUIRE(inv3.has_value());
    CHECK(K.equal(*inv3, K.fromRational(mpq_class(1, 3))));
    auto a = K.generator(0);
    auto q = K.div(a, a);                       // alpha / alpha == 1
    REQUIRE(q.has_value());
    CHECK(K.equal(*q, K.fromRational(1)));
}

TEST_CASE("Tower inverse: zero has no inverse") {
    TowerKernel K(sqrt2Ctx());
    CHECK_FALSE(K.inverse(K.fromRational(0)).has_value());
}

TEST_CASE("Tower inverse two-generator Q(sqrt2, sqrt sqrt2): 1/beta and beta*(1/beta)==1") {
    TowerKernel K(quadTowerCtx());
    auto beta = K.generator(1);                 // sqrt sqrt 2
    auto bi = K.inverse(beta);
    REQUIRE(bi.has_value());
    CHECK(K.equal(K.mul(beta, *bi), K.fromRational(1)));
    // 1/beta == beta^3 / 2  (since beta^4 = 2)
    auto beta3 = K.mul(K.mul(beta, beta), beta);
    auto beta3_half = K.mul(K.fromRational(mpq_class(1, 2)), beta3);
    CHECK(K.equal(*bi, beta3_half));
}

TEST_CASE("Tower inverse two-generator: 1/(alpha+beta) verified by product == 1") {
    TowerKernel K(quadTowerCtx());
    auto e = K.add(K.generator(0), K.generator(1));   // sqrt2 + sqrt sqrt 2
    auto inv = K.inverse(e);
    REQUIRE(inv.has_value());
    CHECK(K.equal(K.mul(e, *inv), K.fromRational(1)));
}
