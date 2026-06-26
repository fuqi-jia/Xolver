// Exact root-membership oracle: the soundness core of Lazard lifting.
// Branch-specific tests (Keep/Drop must distinguish conjugate branches);
// Unknown must never be returned where an exact answer is required here.

#include <doctest/doctest.h>
#include <gmpxx.h>
#include "theory/arith/logics/nra/lazard/RootMembershipOracle.h"

using namespace xolver;

static VarId A0 = VarId{100}, T = VarId{1};

// K = Q(sqrt2), real embedding alpha = +sqrt2 in [7/5, 3/2].
static TowerContext sqrt2Ctx() {
    TowerContext ctx;
    ctx.extensionVars = {A0};
    RationalPolynomial m0; m0.addVar(A0, 2, 1); m0.addConstant(-2); m0.normalize();
    ctx.minimalPolys = {m0};
    AlgebraicRoot ar; ar.lower = mpq_class(7, 5); ar.upper = mpq_class(3, 2);
    ctx.generators = {RealAlg::fromAlgebraic(ar)};
    return ctx;
}
// t^2 - 2 (defining poly of the +-sqrt2 candidates).
static RationalPolynomial defT2m2() {
    RationalPolynomial q; q.addVar(T, 2, 1); q.addConstant(-2); q.normalize(); return q;
}
static const mpq_class posLo(7, 5), posHi(3, 2);     // (1.4, 1.5) brackets +sqrt2
static const mpq_class negLo(-3, 2), negHi(-7, 5);   // (-1.5, -1.4) brackets -sqrt2

TEST_CASE("Oracle test 1: F=t-alpha, keep +sqrt2, drop -sqrt2") {
    RationalPolynomial F; F.addVar(T, 1, 1); F.addVar(A0, 1, -1); F.normalize();   // t - A0
    auto ctx = sqrt2Ctx(); auto q = defT2m2();
    CHECK(lazardRootMembership(F, T, q, posLo, posHi, ctx) == RootMembership::Keep);
    CHECK(lazardRootMembership(F, T, q, negLo, negHi, ctx) == RootMembership::Drop);
}

TEST_CASE("Oracle test 2: F=t+alpha, drop +sqrt2, keep -sqrt2") {
    RationalPolynomial F; F.addVar(T, 1, 1); F.addVar(A0, 1, 1); F.normalize();    // t + A0
    auto ctx = sqrt2Ctx(); auto q = defT2m2();
    CHECK(lazardRootMembership(F, T, q, posLo, posHi, ctx) == RootMembership::Drop);
    CHECK(lazardRootMembership(F, T, q, negLo, negHi, ctx) == RootMembership::Keep);
}

TEST_CASE("Oracle test 3: F=t^2-2, keep both candidates") {
    RationalPolynomial F; F.addVar(T, 2, 1); F.addConstant(-2); F.normalize();
    auto ctx = sqrt2Ctx(); auto q = defT2m2();
    CHECK(lazardRootMembership(F, T, q, posLo, posHi, ctx) == RootMembership::Keep);
    CHECK(lazardRootMembership(F, T, q, negLo, negHi, ctx) == RootMembership::Keep);
}

TEST_CASE("Oracle test 4: conjugate contamination — F=t^2+alpha has no real root") {
    // Norm(t^2+A0) = t^4-2, real roots +-2^{1/4} (the -sqrt2 branch); both Drop.
    RationalPolynomial F; F.addVar(T, 2, 1); F.addVar(A0, 1, 1); F.normalize();
    RationalPolynomial q; q.addVar(T, 4, 1); q.addConstant(-2); q.normalize();     // t^4 - 2
    auto ctx = sqrt2Ctx();
    mpq_class pLo(59, 50), pHi(6, 5);     // (1.18, 1.2) brackets +2^{1/4}
    mpq_class nLo(-6, 5), nHi(-59, 50);
    CHECK(lazardRootMembership(F, T, q, pLo, pHi, ctx) == RootMembership::Drop);
    CHECK(lazardRootMembership(F, T, q, nLo, nHi, ctx) == RootMembership::Drop);
}

TEST_CASE("Oracle test 5: rational beta (exact substitution)") {
    RationalPolynomial F; F.addVar(T, 1, 1); F.addConstant(-1); F.normalize();     // t - 1
    RationalPolynomial q; q.addVar(T, 1, 1); q.addConstant(-1); q.normalize();
    auto ctx = sqrt2Ctx();
    CHECK(lazardRootMembership(F, T, q, mpq_class(1), mpq_class(1), ctx) == RootMembership::Keep);
    CHECK(lazardRootMembership(F, T, q, mpq_class(2), mpq_class(2), ctx) == RootMembership::Drop);
}

TEST_CASE("Oracle test 6/7: beta == generator; reducible defPoly over K (F=t-alpha @ +sqrt2)") {
    // defPoly t^2-2 is reducible over Q(sqrt2); beta=+sqrt2 equals the generator.
    RationalPolynomial F; F.addVar(T, 1, 1); F.addVar(A0, 1, -1); F.normalize();
    auto ctx = sqrt2Ctx(); auto q = defT2m2();
    CHECK(lazardRootMembership(F, T, q, posLo, posHi, ctx) == RootMembership::Keep);
}

TEST_CASE("Oracle soundness: rational beta over a REDUCIBLE tower (m0=A0^2-1)") {
    // m0 = A0^2-1 = (A0-1)(A0+1) is reducible; embedding alpha = +1 in [1/2, 3/2].
    // F = t - A0 at t=1: sub = 1 - A0 reduces to the ring-NONZERO poly (1-A0), yet
    // its real value 1-alpha = 0. A bare ring-nonzero DROP would be UNSOUND; the
    // hardened path uses interval enclosure (box contains 0) => Unknown, NOT Drop.
    TowerContext ctx;
    ctx.extensionVars = {A0};
    RationalPolynomial m0; m0.addVar(A0, 2, 1); m0.addConstant(-1); m0.normalize();
    ctx.minimalPolys = {m0};
    AlgebraicRoot ar; ar.lower = mpq_class(1, 2); ar.upper = mpq_class(3, 2);
    ctx.generators = {RealAlg::fromAlgebraic(ar)};
    RationalPolynomial F; F.addVar(T, 1, 1); F.addVar(A0, 1, -1); F.normalize();   // t - A0
    RationalPolynomial q; q.addVar(T, 1, 1); q.addConstant(-1); q.normalize();      // t - 1
    // beta = 1 (rational); F(1) = 1-alpha truly 0 but ring-nonzero => must be Unknown.
    CHECK(lazardRootMembership(F, T, q, mpq_class(1), mpq_class(1), ctx) == RootMembership::Unknown);
    // beta = 5 (rational); F(5) = 5-alpha, alpha in [1/2,3/2] so 5-alpha in [3.5,4.5]
    // excludes 0 => sound DROP via enclosure.
    RationalPolynomial q2; q2.addVar(T, 1, 1); q2.addConstant(-5); q2.normalize();
    CHECK(lazardRootMembership(F, T, q2, mpq_class(5), mpq_class(5), ctx) == RootMembership::Drop);
}

TEST_CASE("Oracle: tower-coeff F=t-(alpha+1), keep root 1+sqrt2, drop 1-sqrt2") {
    // F = t - A0 - 1; root is 1+sqrt2 (~2.414); Norm = t^2-2t-1 with roots 1+-sqrt2.
    RationalPolynomial F; F.addVar(T, 1, 1); F.addVar(A0, 1, -1); F.addConstant(-1); F.normalize();
    RationalPolynomial q; q.addVar(T, 2, 1); q.addVar(T, 1, -2); q.addConstant(-1); q.normalize();
    auto ctx = sqrt2Ctx();
    mpq_class pLo(24, 10), pHi(25, 10);     // (2.4, 2.5) brackets 1+sqrt2 ~ 2.414
    mpq_class nLo(-5, 10), nHi(-4, 10);     // (-0.5, -0.4) brackets 1-sqrt2 ~ -0.414
    CHECK(lazardRootMembership(F, T, q, pLo, pHi, ctx) == RootMembership::Keep);
    CHECK(lazardRootMembership(F, T, q, nLo, nHi, ctx) == RootMembership::Drop);
}
