// White-box: PolynomialKernel canonical-form equivalence under associativity,
// commutativity, distributivity, and pow-vs-repeated-mul. These are invariants
// the kernel MUST preserve per plan.md §2.3 (polynomial view).
//
// If any case fails, the polynomial view is non-canonical and downstream
// reasoning (CDCAC, NIA factoring, etc.) will silently miss matches.

#include <doctest/doctest.h>
#include <gmpxx.h>
#include "theory/arith/poly/PolynomialKernel.h"

using namespace nlcolver;

TEST_CASE("PolyCanon: x*y == y*x (commutativity)") {
    auto k = createPolynomialKernel();
    auto x = k->mkVar(k->getOrCreateVar("x"));
    auto y = k->mkVar(k->getOrCreateVar("y"));
    CHECK(k->eq(k->mul(x, y), k->mul(y, x)));
}

TEST_CASE("PolyCanon: (x+y)+z == x+(y+z) (associativity)") {
    auto k = createPolynomialKernel();
    auto x = k->mkVar(k->getOrCreateVar("x"));
    auto y = k->mkVar(k->getOrCreateVar("y"));
    auto z = k->mkVar(k->getOrCreateVar("z"));
    CHECK(k->eq(k->add(k->add(x, y), z), k->add(x, k->add(y, z))));
}

TEST_CASE("PolyCanon: x*x*x == x^3 (pow vs repeated mul)") {
    auto k = createPolynomialKernel();
    auto x = k->mkVar(k->getOrCreateVar("x"));
    auto cubed_by_mul = k->mul(k->mul(x, x), x);
    auto cubed_by_pow = k->pow(x, 3);
    CHECK(k->eq(cubed_by_mul, cubed_by_pow));
}

TEST_CASE("PolyCanon: x*(y+z) == x*y + x*z (distributivity)") {
    auto k = createPolynomialKernel();
    auto x = k->mkVar(k->getOrCreateVar("x"));
    auto y = k->mkVar(k->getOrCreateVar("y"));
    auto z = k->mkVar(k->getOrCreateVar("z"));
    auto lhs = k->mul(x, k->add(y, z));
    auto rhs = k->add(k->mul(x, y), k->mul(x, z));
    CHECK(k->eq(lhs, rhs));
}

TEST_CASE("PolyCanon: 2*x + 3*x == 5*x (linear combine)") {
    auto k = createPolynomialKernel();
    auto x = k->mkVar(k->getOrCreateVar("x"));
    auto lhs = k->add(k->mul(k->mkConst(2), x), k->mul(k->mkConst(3), x));
    auto rhs = k->mul(k->mkConst(5), x);
    CHECK(k->eq(lhs, rhs));
}

TEST_CASE("PolyCanon: x - x == 0 (cancellation)") {
    auto k = createPolynomialKernel();
    auto x = k->mkVar(k->getOrCreateVar("x"));
    auto diff = k->sub(x, x);
    CHECK(k->isZero(diff));
}

TEST_CASE("PolyCanon: 0*x == 0 (annihilator)") {
    auto k = createPolynomialKernel();
    auto x = k->mkVar(k->getOrCreateVar("x"));
    auto zero_times_x = k->mul(k->mkZero(), x);
    CHECK(k->isZero(zero_times_x));
}

TEST_CASE("PolyCanon: 1*x == x (identity)") {
    auto k = createPolynomialKernel();
    auto x = k->mkVar(k->getOrCreateVar("x"));
    auto one_times_x = k->mul(k->mkOne(), x);
    CHECK(k->eq(one_times_x, x));
}

TEST_CASE("PolyCanon: (x+1)*(x-1) == x*x - 1 (FOIL)") {
    auto k = createPolynomialKernel();
    auto x = k->mkVar(k->getOrCreateVar("x"));
    auto one = k->mkOne();
    auto lhs = k->mul(k->add(x, one), k->sub(x, one));
    auto rhs = k->sub(k->mul(x, x), one);
    CHECK(k->eq(lhs, rhs));
}

TEST_CASE("PolyCanon: (x+y)^2 == x^2 + 2xy + y^2 (binomial)") {
    auto k = createPolynomialKernel();
    auto x = k->mkVar(k->getOrCreateVar("x"));
    auto y = k->mkVar(k->getOrCreateVar("y"));
    auto lhs = k->pow(k->add(x, y), 2);
    auto x2 = k->mul(x, x);
    auto y2 = k->mul(y, y);
    auto two_xy = k->mul(k->mkConst(2), k->mul(x, y));
    auto rhs = k->add(k->add(x2, two_xy), y2);
    CHECK(k->eq(lhs, rhs));
}

TEST_CASE("PolyCanon: neg vs subtract-from-zero") {
    auto k = createPolynomialKernel();
    auto x = k->mkVar(k->getOrCreateVar("x"));
    CHECK(k->eq(k->neg(x), k->sub(k->mkZero(), x)));
}

TEST_CASE("PolyCanon: variables() lists only nontrivially-appearing vars") {
    auto k = createPolynomialKernel();
    auto x = k->mkVar(k->getOrCreateVar("x"));
    auto y = k->mkVar(k->getOrCreateVar("y"));
    // y is added then subtracted, net coefficient is 0 — should not appear.
    auto p = k->sub(k->add(x, y), y);
    auto vs = k->variables(p);
    auto has_y = std::find(vs.begin(), vs.end(), "y") != vs.end();
    CHECK_FALSE(has_y);
}
