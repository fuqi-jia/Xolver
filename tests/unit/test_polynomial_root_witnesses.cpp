// White-box: PolynomialKernel.sgn at strategic sample points to verify root
// localization invariants. This is a black-box proxy for Sturm sequences —
// the kernel does not directly expose Sturm chains, but sgn at well-chosen
// rationals tells us where sign changes occur.
//
// Invariant of any consistent polynomial backend:
//   1. constant polynomial sgn always agrees with its value.
//   2. p(0) sgn equals sgn of constant coefficient.
//   3. For p with bracketed roots [a, b], sgn(p(a)) != sgn(p(b)).
//   4. For sum of squares, sgn ≥ 0 at every rational sample.

#include <doctest/doctest.h>
#include <gmpxx.h>
#include "theory/arith/poly/PolynomialKernel.h"

using namespace xolver;

static std::unordered_map<std::string, mpq_class> point(const std::string& v, const mpq_class& val) {
    return {{v, val}};
}

TEST_CASE("Sturm/sgn: constant polynomial p=5 has sgn=+1 anywhere") {
    auto k = createPolynomialKernel();
    auto five = k->mkConst(5);
    CHECK(k->sgn(five, point("x", 0))  > 0);
    CHECK(k->sgn(five, point("x", -100)) > 0);
}

TEST_CASE("Sturm/sgn: constant polynomial p=-3 has sgn=-1") {
    auto k = createPolynomialKernel();
    auto neg3 = k->mkConst(-3);
    CHECK(k->sgn(neg3, point("x", 0)) < 0);
}

TEST_CASE("Sturm/sgn: zero polynomial has sgn=0") {
    auto k = createPolynomialKernel();
    auto z = k->mkZero();
    CHECK(k->sgn(z, point("x", 7)) == 0);
}

TEST_CASE("Sturm/sgn: x has sgn equal to sgn of sample") {
    auto k = createPolynomialKernel();
    auto x = k->mkVar(k->getOrCreateVar("x"));
    CHECK(k->sgn(x, point("x",  5)) > 0);
    CHECK(k->sgn(x, point("x", -5)) < 0);
    CHECK(k->sgn(x, point("x",  0)) == 0);
}

TEST_CASE("Sturm/sgn: x^2 is non-negative everywhere") {
    auto k = createPolynomialKernel();
    auto x = k->mkVar(k->getOrCreateVar("x"));
    auto xsq = k->mul(x, x);
    CHECK(k->sgn(xsq, point("x",  3)) > 0);
    CHECK(k->sgn(xsq, point("x", -3)) > 0);
    CHECK(k->sgn(xsq, point("x",  0)) == 0);
}

TEST_CASE("Sturm/sgn: x^2 - 4 brackets roots at ±2") {
    auto k = createPolynomialKernel();
    auto x = k->mkVar(k->getOrCreateVar("x"));
    auto p = k->sub(k->mul(x, x), k->mkConst(4));
    // p(0) = -4 < 0; p(3) = 5 > 0; p(-3) = 5 > 0 — two sign changes (two roots).
    CHECK(k->sgn(p, point("x", 0))  < 0);
    CHECK(k->sgn(p, point("x", 3))  > 0);
    CHECK(k->sgn(p, point("x", -3)) > 0);
    CHECK(k->sgn(p, point("x", 2))  == 0);  // exact root
    CHECK(k->sgn(p, point("x", -2)) == 0);  // exact root
}

TEST_CASE("Sturm/sgn: x^3 - x has roots at -1, 0, 1") {
    auto k = createPolynomialKernel();
    auto x  = k->mkVar(k->getOrCreateVar("x"));
    auto x3 = k->mul(k->mul(x, x), x);
    auto p  = k->sub(x3, x);
    CHECK(k->sgn(p, point("x", -1)) == 0);
    CHECK(k->sgn(p, point("x",  0)) == 0);
    CHECK(k->sgn(p, point("x",  1)) == 0);
    // Between roots, sign alternates: p(-2) = -6, p(-0.5) = 3/8, p(0.5) = -3/8, p(2) = 6.
    CHECK(k->sgn(p, point("x", -2)) < 0);
    CHECK(k->sgn(p, point("x",  2)) > 0);
}

TEST_CASE("Sturm/sgn: x^2 + 1 is strictly positive (no real root)") {
    auto k = createPolynomialKernel();
    auto x = k->mkVar(k->getOrCreateVar("x"));
    auto p = k->add(k->mul(x, x), k->mkOne());
    CHECK(k->sgn(p, point("x",  0)) > 0);
    CHECK(k->sgn(p, point("x",  100)) > 0);
    CHECK(k->sgn(p, point("x", -100)) > 0);
}

TEST_CASE("Sturm/sgn: bivariate x^2 + y^2 is non-negative") {
    auto k = createPolynomialKernel();
    auto x = k->mkVar(k->getOrCreateVar("x"));
    auto y = k->mkVar(k->getOrCreateVar("y"));
    auto sos = k->add(k->mul(x, x), k->mul(y, y));
    std::unordered_map<std::string, mpq_class> s = {{"x", 3}, {"y", 4}};
    CHECK(k->sgn(sos, s) > 0);
    s = {{"x", 0}, {"y", 0}};
    CHECK(k->sgn(sos, s) == 0);
    s = {{"x", -2}, {"y", -2}};
    CHECK(k->sgn(sos, s) > 0);
}

TEST_CASE("Sturm/sgn: degree-4 (x^2-1)(x^2-4) — 4 real roots ±1, ±2") {
    auto k = createPolynomialKernel();
    auto x = k->mkVar(k->getOrCreateVar("x"));
    auto a = k->sub(k->mul(x, x), k->mkOne());
    auto b = k->sub(k->mul(x, x), k->mkConst(4));
    auto p = k->mul(a, b);
    // Check sample sign changes across (-3, -2, -1.5, -1, 0, 1, 1.5, 2, 3).
    CHECK(k->sgn(p, point("x", -3)) > 0);
    CHECK(k->sgn(p, point("x", -2)) == 0);
    CHECK(k->sgn(p, point("x", mpq_class(-3, 2))) < 0);  // -1.5
    CHECK(k->sgn(p, point("x", -1)) == 0);
    CHECK(k->sgn(p, point("x",  0)) > 0);
    CHECK(k->sgn(p, point("x",  1)) == 0);
    CHECK(k->sgn(p, point("x", mpq_class(3, 2))) < 0);   // 1.5
    CHECK(k->sgn(p, point("x",  2)) == 0);
    CHECK(k->sgn(p, point("x",  3)) > 0);
}

TEST_CASE("Sturm/sgn: integer evaluation matches rational evaluation on int point") {
    auto k = createPolynomialKernel();
    auto x = k->mkVar(k->getOrCreateVar("x"));
    auto p = k->sub(k->mul(x, x), k->mkConst(9));
    auto rat_sgn = k->sgn(p, point("x", 3));
    CHECK(rat_sgn == 0);
    auto eval = k->evalInteger(p, {{"x", mpz_class(3)}});
    if (eval.has_value()) CHECK(*eval == 0);
}
