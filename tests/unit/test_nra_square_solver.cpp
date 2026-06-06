// Unit tests for the NRA algebraic square-cascade FOUNDATION (NraSquareSolver):
// detecting a*x^2 + b = 0 square equalities and resolving x to a rational or
// algebraic root. This is the seed of the algebraic-SAT model construction for
// the square-defined QF_NRA gap (e.g. Geogebra IsoRightTriangle, model in Q(sqrt2)).
#include <doctest/doctest.h>
#include <gmpxx.h>

#include "theory/arith/nra/NraSquareSolver.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include "theory/arith/poly/RationalPolynomial.h"

using namespace xolver;

TEST_CASE("rationalSqrt: perfect vs non-perfect rational squares") {
    mpq_class root;
    CHECK(rationalSqrt(mpq_class(1, 4), root));
    CHECK(root == mpq_class(1, 2));
    CHECK(rationalSqrt(mpq_class(4, 9), root));
    CHECK(root == mpq_class(2, 3));
    CHECK(rationalSqrt(mpq_class(0, 1), root));
    CHECK(root == mpq_class(0, 1));
    CHECK(rationalSqrt(mpq_class(25, 16), root));
    CHECK(root == mpq_class(5, 4));
    CHECK_FALSE(rationalSqrt(mpq_class(1, 2), root));   // 1/2 irrational sqrt
    CHECK_FALSE(rationalSqrt(mpq_class(2, 1), root));   // sqrt2
    CHECK_FALSE(rationalSqrt(mpq_class(1, 3), root));
    CHECK_FALSE(rationalSqrt(mpq_class(-1, 4), root));  // negative
}

TEST_CASE("detectSquareEqualities + solveSquareRoot: rational and algebraic roots") {
    auto kp = createPolynomialKernel();
    PolynomialKernel& k = *kp;
    VarId x = k.getOrCreateVar("x");
    VarId y = k.getOrCreateVar("y");

    // -4 x^2 + 1 = 0  =>  x^2 = 1/4  (perfect square => x rational)
    RationalPolynomial e1;
    e1.addVar(x, 2, mpq_class(-4));
    e1.addConstant(mpq_class(1));
    e1.normalize();
    // -2 y^2 + 1 = 0  =>  y^2 = 1/2  (=> y algebraic, root of -2y^2+1)
    RationalPolynomial e2;
    e2.addVar(y, 2, mpq_class(-2));
    e2.addConstant(mpq_class(1));
    e2.normalize();
    // x + y - 1 = 0   (two variables => NOT a square equality; must be ignored)
    RationalPolynomial e3;
    e3.addVar(x, 1, mpq_class(1));
    e3.addVar(y, 1, mpq_class(1));
    e3.addConstant(mpq_class(-1));
    e3.normalize();

    std::vector<std::pair<PolyId, Relation>> eqs = {
        {e1.toPolyId(k), Relation::Eq},
        {e2.toPolyId(k), Relation::Eq},
        {e3.toPolyId(k), Relation::Eq},
    };

    auto sqs = detectSquareEqualities(eqs, k);
    REQUIRE(sqs.size() == 2);   // e1 and e2 only; e3 (two vars) filtered

    const SquareEquality* sx = nullptr;
    const SquareEquality* sy = nullptr;
    for (const auto& s : sqs) {
        if (s.var == x) sx = &s;
        if (s.var == y) sy = &s;
    }
    REQUIRE(sx);
    REQUIRE(sy);
    CHECK(sx->squaredValue == mpq_class(1, 4));
    CHECK(sy->squaredValue == mpq_class(1, 2));

    // x: perfect square => rational, sign-selected.
    SquareRoot rx = solveSquareRoot(*sx, +1);
    CHECK(rx.feasible);
    CHECK(rx.isRational);
    CHECK(rx.rationalValue == mpq_class(1, 2));
    SquareRoot rxn = solveSquareRoot(*sx, -1);
    CHECK(rxn.rationalValue == mpq_class(-1, 2));

    // y: not a perfect square => algebraic.
    SquareRoot ry = solveSquareRoot(*sy, +1);
    CHECK(ry.feasible);
    CHECK_FALSE(ry.isRational);
    CHECK(ry.squaredValue == mpq_class(1, 2));
    CHECK(ry.sign == 1);
}

TEST_CASE("solveSquareRoot: negative squared value is infeasible") {
    SquareEquality sq;
    sq.var = VarId{0};
    sq.squaredValue = mpq_class(-3, 4);
    sq.constraintIndex = 0;
    SquareRoot r = solveSquareRoot(sq, +1);
    CHECK_FALSE(r.feasible);   // x^2 = -3/4 has no real root
}

TEST_CASE("substituteVarWithVar: collapses v11*v12 to v11^2") {
    auto kp = createPolynomialKernel();
    PolynomialKernel& k = *kp;
    VarId v11 = k.getOrCreateVar("v11");
    VarId v12 = k.getOrCreateVar("v12");

    // p = v11 * v12  -> substitute v12 := v11 -> v11^2
    PolyId p = k.mul(k.mkVar(v11), k.mkVar(v12));
    PolyId p2 = substituteVarWithVar(p, v12, v11, k);
    auto vars = k.variables(p2);
    REQUIRE(vars.size() == 1);
    CHECK(vars[0] == "v11");
    REQUIRE(k.degree(p2, "v11"));
    CHECK(*k.degree(p2, "v11") == 2);
    CHECK(k.isZero(k.sub(p2, k.mul(k.mkVar(v11), k.mkVar(v11)))));   // p2 == v11^2

    // A more 14b-like reduction: v11^3*v12 + v11 - 1 with v12:=v11 -> v11^4 + v11 - 1
    PolyId q = k.add(k.sub(k.mul(k.pow(k.mkVar(v11), 3), k.mkVar(v12)), k.mkConst(1)),
                     k.mkVar(v11));
    PolyId q2 = substituteVarWithVar(q, v12, v11, k);
    auto qexpect = k.add(k.sub(k.pow(k.mkVar(v11), 4), k.mkConst(1)), k.mkVar(v11));
    CHECK(k.isZero(k.sub(q2, qexpect)));

    // No-op when from == to.
    CHECK(substituteVarWithVar(p, v11, v11, k) == p);
}

TEST_CASE("collapseAlgebraicRoots: equal (c,sign) share a generator") {
    std::vector<SquareRoot> roots;
    // v11: algebraic sqrt(1/2), +
    roots.push_back({VarId{10}, true, false, mpq_class(0), mpq_class(1, 2), +1});
    // v12: algebraic sqrt(1/2), +  -> SAME number as v11
    roots.push_back({VarId{11}, true, false, mpq_class(0), mpq_class(1, 2), +1});
    // v10: rational 1/2 (from x^2 = 1/4)
    roots.push_back({VarId{12}, true, true, mpq_class(1, 2), mpq_class(1, 4), +1});
    // w: algebraic sqrt(1/2), -  -> DIFFERENT (negative root)
    roots.push_back({VarId{13}, true, false, mpq_class(0), mpq_class(1, 2), -1});

    CollapsedRoots c = collapseAlgebraicRoots(roots);
    CHECK(c.feasible);
    REQUIRE(c.rationalVars.count(VarId{12}));
    CHECK(c.rationalVars.at(VarId{12}) == mpq_class(1, 2));
    CHECK(c.generators.size() == 2);                 // {1/2,+} and {1/2,-}
    CHECK(c.aliasOf.at(VarId{10}) == VarId{10});     // representative -> self
    CHECK(c.aliasOf.at(VarId{11}) == VarId{10});     // v12 collapses onto v11
    CHECK(c.aliasOf.at(VarId{13}) == VarId{13});     // negative-root generator distinct
    CHECK(c.genSquared.at(VarId{10}) == mpq_class(1, 2));
    CHECK(c.genSign.at(VarId{13}) == -1);
}

TEST_CASE("collapseAlgebraicRoots: infeasible when a squared value is negative") {
    std::vector<SquareRoot> roots;
    roots.push_back({VarId{1}, false, false, mpq_class(0), mpq_class(-1, 4), +1});
    CollapsedRoots c = collapseAlgebraicRoots(roots);
    CHECK_FALSE(c.feasible);
}
