// Exact real-root isolation via Sturm sequences (self-contained ℚ arithmetic).
// Each reported interval must bracket exactly one real root; count must match.

#include <doctest/doctest.h>
#include <gmpxx.h>
#include "theory/arith/nra/valuation/RationalRootIsolation.h"

using namespace xolver;

static VarId X = VarId{1};

static mpq_class evalAt(const RationalPolynomial& p, const mpq_class& v) {
    RationalPolynomial s = p.substituteRational(X, v); s.normalize();
    return s.isZero() ? mpq_class(0) : s.constantValue();
}
// Every interval brackets a root of p; intervals are disjoint & ascending.
static void checkBrackets(const RationalPolynomial& p, const RationalRootResult& r) {
    REQUIRE(r.ok);
    mpq_class prevHi;
    bool first = true;
    for (const auto& iv : r.roots) {
        CHECK(iv.lo <= iv.hi);
        if (iv.isPoint()) {
            CHECK(evalAt(p, iv.lo) == 0);
        } else {
            mpq_class flo = evalAt(p, iv.lo), fhi = evalAt(p, iv.hi);
            CHECK(flo != 0); CHECK(fhi != 0);
            CHECK(flo * fhi < 0);                 // odd # roots; isolated => exactly 1
        }
        if (!first) CHECK(prevHi <= iv.lo);       // disjoint, ascending
        prevHi = iv.hi; first = false;
    }
}

TEST_CASE("Sturm: x^2 - 2 has two real roots (±sqrt2)") {
    RationalPolynomial p; p.addVar(X, 2, 1); p.addConstant(-2); p.normalize();
    auto r = isolateRationalRoots(p, X);
    CHECK(r.roots.size() == 2);
    checkBrackets(p, r);
}

TEST_CASE("Sturm: x^2 + 1 has no real roots") {
    RationalPolynomial p; p.addVar(X, 2, 1); p.addConstant(1); p.normalize();
    auto r = isolateRationalRoots(p, X);
    CHECK(r.ok);
    CHECK(r.roots.empty());
}

TEST_CASE("Sturm: x^3 - x has three roots (-1, 0, 1)") {
    RationalPolynomial p; p.addVar(X, 3, 1); p.addVar(X, 1, -1); p.normalize();
    auto r = isolateRationalRoots(p, X);
    CHECK(r.roots.size() == 3);
    checkBrackets(p, r);
}

TEST_CASE("Sturm: (x-1)(x-2)(x-3) has three roots") {
    // x^3 - 6x^2 + 11x - 6
    RationalPolynomial p; p.addVar(X, 3, 1); p.addVar(X, 2, -6); p.addVar(X, 1, 11); p.addConstant(-6);
    p.normalize();
    auto r = isolateRationalRoots(p, X);
    CHECK(r.roots.size() == 3);
    checkBrackets(p, r);
}

TEST_CASE("Sturm: (x-1)^2 has one distinct root (squarefree); double root => no sign change") {
    RationalPolynomial p; p.addVar(X, 2, 1); p.addVar(X, 1, -2); p.addConstant(1); p.normalize();
    auto r = isolateRationalRoots(p, X);
    REQUIRE(r.roots.size() == 1);
    // A double root touches zero without a sign change, so verify containment of
    // the known root x=1 instead of a bracket sign change.
    const auto& iv = r.roots[0];
    CHECK(iv.lo < mpq_class(1));
    CHECK(mpq_class(1) <= iv.hi);
    CHECK(evalAt(p, mpq_class(1)) == 0);
}

TEST_CASE("Sturm: x^5 - 5x^3 + 4x has five roots (-2,-1,0,1,2)") {
    RationalPolynomial p; p.addVar(X, 5, 1); p.addVar(X, 3, -5); p.addVar(X, 1, 4); p.normalize();
    auto r = isolateRationalRoots(p, X);
    CHECK(r.roots.size() == 5);
    checkBrackets(p, r);
}

TEST_CASE("Sturm: rational roots with fractional coefficients (x-1/2)(x+3/2)") {
    // (x-1/2)(x+3/2) = x^2 + x - 3/4
    RationalPolynomial p; p.addVar(X, 2, 1); p.addVar(X, 1, 1);
    p.addConstant(mpq_class(-3, 4)); p.normalize();
    auto r = isolateRationalRoots(p, X);
    CHECK(r.roots.size() == 2);
    checkBrackets(p, r);
}

TEST_CASE("Sturm: non-univariate input reports ok=false") {
    RationalPolynomial p; p.addVar(X, 2, 1); p.addVar(VarId{2}, 1, 1); p.normalize();  // x^2 + y
    auto r = isolateRationalRoots(p, X);
    CHECK_FALSE(r.ok);
}
