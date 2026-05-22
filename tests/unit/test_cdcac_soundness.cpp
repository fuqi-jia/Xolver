#include <doctest/doctest.h>
#include "theory/arith/nra/backend/LibpolyBackend.h"
#include "theory/arith/nra/core/CdcacCore.h"
#include "theory/arith/poly/PolynomialKernel.h"

using namespace nlcolver;

// ------------------------------------------------------------------
// Test A: Endpoint same-sign shortcut is unsound (reviewer counterexample)
//
// alpha = sqrt(2), interval [1, 2]
// g(x) = 25*x^2 - 70*x + 48  ( = 25*(x-6/5)*(x-8/5) )
//
// g(1) = 3 > 0, g(2) = 8 > 0  (endpoints same sign)
// gcd(x^2 - 2, g) = 1         (coprime)
// BUT g(sqrt(2)) = 98 - 70*sqrt(2) < 0
//
// A broken shortcut would return Pos; the correct answer is Neg.
// ------------------------------------------------------------------
TEST_CASE("A: endpoint same-sign + GCD=1 does NOT determine sign") {
    auto kernel = createPolynomialKernel();
    LibpolyBackend algebra(kernel.get());

    // defining poly for sqrt(2): x^2 - 2
    UniPolyId defPoly = algebra.allocUni({1, 0, -2});

    // g(x) = 25x^2 - 70x + 48
    UniPolyId g = algebra.allocUni({25, -70, 48});

    AlgebraicRoot alpha;
    alpha.definingPoly = defPoly;
    alpha.rootIndex = 1;   // positive root: sqrt(2)
    alpha.lower = mpq_class(1);
    alpha.upper = mpq_class(2);

    Sign s = algebra.signUnivariateAtAlgebraic(g, alpha);
    CHECK(s == Sign::Neg);
}

// ------------------------------------------------------------------
// Test B: Rational inside algebraic interval does NOT imply equality
//
// alpha = sqrt(2), interval [1, 2]
// q = 3/2 = 1.5
//
// 3/2 ∈ [1, 2] but 3/2 != sqrt(2).
// compareRealAlg must NOT return Equal.
// ------------------------------------------------------------------
TEST_CASE("B: rational inside interval but not equal to algebraic root") {
    auto kernel = createPolynomialKernel();
    LibpolyBackend algebra(kernel.get());

    UniPolyId defPoly = algebra.allocUni({1, 0, -2});

    AlgebraicRoot alpha;
    alpha.definingPoly = defPoly;
    alpha.rootIndex = 1;
    alpha.lower = mpq_class(1);
    alpha.upper = mpq_class(2);

    RealAlg alg = RealAlg::fromAlgebraic(alpha);
    RealAlg rat = RealAlg::fromRational(mpq_class(3, 2));

    CompareResult c1 = algebra.compareRealAlg(rat, alg);
    CompareResult c2 = algebra.compareRealAlg(alg, rat);

    // The critical soundness requirement: must NOT return Equal.
    // compareRealAlg first checks defPoly(q)==0; since 1.5^2-2 != 0,
    // it knows q != alpha.  It then tries to refine the interval to
    // separate q from alpha.  If refinement succeeds, it returns Less
    // or Greater.  If max refinement is exhausted without separation,
    // it conservatively returns Unknown.  All three outcomes are sound.
    CHECK(c1 != CompareResult::Equal);
    CHECK(c2 != CompareResult::Equal);

    // If not Unknown, the two directions must be opposite.
    if (c1 != CompareResult::Unknown && c2 != CompareResult::Unknown) {
        CHECK(((c1 == CompareResult::Less && c2 == CompareResult::Greater) ||
               (c1 == CompareResult::Greater && c2 == CompareResult::Less)));
    }
}

// ------------------------------------------------------------------
// Test C: True rational-algebraic equality IS detected
//
// defining poly: 4*x^2 - 1, positive root is 1/2.
// q = 1/2.
// compareRealAlg must return Equal.
// ------------------------------------------------------------------
TEST_CASE("C: true rational-algebraic equality detected by defPoly(q)==0") {
    auto kernel = createPolynomialKernel();
    LibpolyBackend algebra(kernel.get());

    UniPolyId defPoly = algebra.allocUni({4, 0, -1});

    AlgebraicRoot alpha;
    alpha.definingPoly = defPoly;
    alpha.rootIndex = 1;   // positive root: 1/2
    alpha.lower = mpq_class(0);
    alpha.upper = mpq_class(1);

    RealAlg alg = RealAlg::fromAlgebraic(alpha);
    RealAlg rat = RealAlg::fromRational(mpq_class(1, 2));

    CompareResult c = algebra.compareRealAlg(rat, alg);
    CHECK(c == CompareResult::Equal);
}

// ------------------------------------------------------------------
// Test D: target-variable pseudo-remainder invariant
//
// f = y - x^2
// g = x^2 - 2
// target variable = x
//
// Expected remainder r should satisfy:
//   scale * f = q * g + r
//   degree_x(r) < degree_x(g) = 2
//
// In particular, one valid result is r = y - 2, scale = 1.
// ------------------------------------------------------------------
TEST_CASE("D: pseudoRemainderWithScale invariant") {
    auto kernel = createPolynomialKernel();

    VarId x = kernel->getOrCreateVar("x");
    VarId y = kernel->getOrCreateVar("y");

    // f = y - x^2
    PolyId f = kernel->add(kernel->mkVar(y), kernel->neg(kernel->pow(kernel->mkVar(x), 2)));

    // g = x^2 - 2
    PolyId g = kernel->add(kernel->pow(kernel->mkVar(x), 2), kernel->mkConst(mpq_class(-2)));

    auto pr = kernel->pseudoRemainderWithScale(f, g, x);
    REQUIRE(pr.ok());

    PolyId r = pr.remainder;
    PolyId scale = pr.scaleFactor;
    int k = pr.exponent;

    // degree_x(r) < degree_x(g) = 2
    auto degR = kernel->degree(r, "x");
    auto degG = kernel->degree(g, "x");
    REQUIRE(degR.has_value());
    REQUIRE(degG.has_value());
    CHECK(*degR < *degG);

    // scale * f = q * g + r  for some quotient q
    // We verify by checking scale*f - r is divisible by g.
    // Since we don't have exact division exposed, we check via pseudo-remainder:
    // prem(scale*f - r, g) should be Zero.
    PolyId scaledF = kernel->mul(scale, f);
    PolyId lhs = kernel->sub(scaledF, r);
    auto divCheck = kernel->pseudoRemainder(lhs, g);
    REQUIRE(divCheck.has_value());
    CHECK(kernel->isZero(*divCheck));

    // Additionally, for this specific case the remainder should be y - 2.
    // We check this by evaluating at a sample point.
    std::unordered_map<std::string, mpq_class> sample;
    sample["x"] = mpq_class(0);
    sample["y"] = mpq_class(5);
    int sgnR = kernel->sgn(r, sample);
    // r(0, 5) = 5 - 2 = 3 > 0
    CHECK(sgnR > 0);

    sample["y"] = mpq_class(2);
    sgnR = kernel->sgn(r, sample);
    // r(0, 2) = 2 - 2 = 0
    CHECK(sgnR == 0);
}
