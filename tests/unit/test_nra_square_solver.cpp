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

TEST_CASE("signOfRootExpr: sign of a*sqrt(c) + b (exact)") {
    const mpq_class two(2);
    CHECK(signOfRootExpr(mpq_class(1), mpq_class(1), two) == 1);    // sqrt2 + 1 > 0
    CHECK(signOfRootExpr(mpq_class(1), mpq_class(-2), two) == -1);  // sqrt2 - 2 < 0
    CHECK(signOfRootExpr(mpq_class(1), mpq_class(-1), two) == 1);   // sqrt2 - 1 > 0
    CHECK(signOfRootExpr(mpq_class(-1), mpq_class(1), two) == -1);  // -sqrt2 + 1 < 0
    CHECK(signOfRootExpr(mpq_class(2), mpq_class(-3), two) == -1);  // 2sqrt2 - 3 < 0
    CHECK(signOfRootExpr(mpq_class(2), mpq_class(-2), two) == 1);   // 2sqrt2 - 2 > 0
    CHECK(signOfRootExpr(mpq_class(0), mpq_class(-3), two) == -1);  // pure -3
    CHECK(signOfRootExpr(mpq_class(5), mpq_class(0), two) == 1);    // 5 sqrt2 > 0
    CHECK(signOfRootExpr(mpq_class(0), mpq_class(0), two) == 0);    // exactly 0
    // The exact boundary: a^2 c == b^2  => a*sqrt(c)+b is 0 only if signs oppose.
    CHECK(signOfRootExpr(mpq_class(1), mpq_class(-1), mpq_class(1)) == 0);  // sqrt1 - 1 = 0
}

TEST_CASE("signOfPolyAtGenerator: validate over a single generator x = +sqrt(1/2)") {
    auto kp = createPolynomialKernel();
    PolynomialKernel& k = *kp;
    VarId g = k.getOrCreateVar("g");
    const mpq_class c(1, 2);   // g^2 = 1/2, g = +sqrt(1/2)

    auto sgnOf = [&](const RationalPolynomial& rp) {
        return signOfPolyAtGenerator(rp, g, c, +1);
    };

    // g^2 - 1/2  == 0   (the defining relation reduces to 0)
    RationalPolynomial p1; p1.addVar(g, 2, mpq_class(1)); p1.addConstant(mpq_class(-1, 2)); p1.normalize();
    REQUIRE(sgnOf(p1)); CHECK(*sgnOf(p1) == 0);

    // (4/5) g + 2/5  > 0   (the derived m = (4/5)sqrt(1/2)+2/5 ~ 0.966)
    RationalPolynomial p2; p2.addVar(g, 1, mpq_class(4, 5)); p2.addConstant(mpq_class(2, 5)); p2.normalize();
    REQUIRE(sgnOf(p2)); CHECK(*sgnOf(p2) == 1);

    // g  > 0
    RationalPolynomial p3; p3.addVar(g, 1, mpq_class(1)); p3.normalize();
    REQUIRE(sgnOf(p3)); CHECK(*sgnOf(p3) == 1);

    // g - 1 < 0   (sqrt(1/2) ~ 0.707 < 1)
    RationalPolynomial p4; p4.addVar(g, 1, mpq_class(1)); p4.addConstant(mpq_class(-1)); p4.normalize();
    REQUIRE(sgnOf(p4)); CHECK(*sgnOf(p4) == -1);

    // 2g - 1 > 0   (2*0.707 - 1 ~ 0.41)
    RationalPolynomial p5; p5.addVar(g, 1, mpq_class(2)); p5.addConstant(mpq_class(-1)); p5.normalize();
    REQUIRE(sgnOf(p5)); CHECK(*sgnOf(p5) == 1);

    // higher degree: g^3 reduces to (1/2) g  > 0
    RationalPolynomial p6; p6.addVar(g, 3, mpq_class(1)); p6.normalize();
    REQUIRE(sgnOf(p6)); CHECK(*sgnOf(p6) == 1);

    // negative generator g = -sqrt(1/2): g > 0 is FALSE (sign -1)
    RationalPolynomial p7; p7.addVar(g, 1, mpq_class(1)); p7.normalize();
    auto s7 = signOfPolyAtGenerator(p7, g, c, -1);
    REQUIRE(s7); CHECK(*s7 == -1);

    // a poly mentioning another variable => nullopt (caller must substitute first)
    VarId h = k.getOrCreateVar("h");
    RationalPolynomial p8; p8.addVar(g, 1, mpq_class(1)); p8.addVar(h, 1, mpq_class(1)); p8.normalize();
    CHECK_FALSE(signOfPolyAtGenerator(p8, g, c, +1));
}

TEST_CASE("trySquareCascade: decides the Geogebra Bottema1_14b structure SAT (Q(sqrt2))") {
    auto kp = createPolynomialKernel();
    PolynomialKernel& k = *kp;
    VarId m = k.getOrCreateVar("m");
    VarId v10 = k.getOrCreateVar("v10");
    VarId v11 = k.getOrCreateVar("v11");
    VarId v12 = k.getOrCreateVar("v12");
    VarId v13 = k.getOrCreateVar("v13");
    auto V = [&](VarId v) { return k.mkVar(v); };
    auto C = [&](int n) { return k.mkConst(mpq_class(n)); };

    // squares:  -4 v10^2 + 1 = 0 ;  4 v10^2 - 4 v11^2 + 1 = 0 ;  same for v12 ;  -v13 + 1 = 0
    PolyId e10 = k.add(k.mul(C(-4), k.pow(V(v10), 2)), C(1));
    PolyId e11 = k.add(k.sub(k.mul(C(4), k.pow(V(v10), 2)), k.mul(C(4), k.pow(V(v11), 2))), C(1));
    PolyId e12 = k.add(k.sub(k.mul(C(4), k.pow(V(v10), 2)), k.mul(C(4), k.pow(V(v12), 2))), C(1));
    PolyId e13 = k.add(k.neg(V(v13)), C(1));

    // big eq:  v11^3 v12^2 + v11^2 v12^3 + v11^2 v12^2
    //        - m v11^3 v12^3 - m v11^3 v12 - m v11 v12^3  =  0   (linear in m)
    PolyId t1 = k.mul(k.mul(V(m), k.pow(V(v11), 3)), k.pow(V(v12), 3));
    PolyId t2 = k.mul(k.mul(V(m), k.pow(V(v11), 3)), V(v12));
    PolyId t3 = k.mul(k.mul(V(m), V(v11)), k.pow(V(v12), 3));
    PolyId t4 = k.mul(k.pow(V(v11), 3), k.pow(V(v12), 2));
    PolyId t5 = k.mul(k.pow(V(v11), 2), k.pow(V(v12), 3));
    PolyId t6 = k.mul(k.pow(V(v11), 2), k.pow(V(v12), 2));
    PolyId big = k.sub(k.sub(k.sub(k.add(k.add(t4, t5), t6), t1), t2), t3);

    std::vector<std::pair<PolyId, Relation>> cons = {
        {V(m), Relation::Gt}, {V(v12), Relation::Gt}, {V(v11), Relation::Gt}, {V(v13), Relation::Gt},
        {e10, Relation::Eq}, {e11, Relation::Eq}, {e12, Relation::Eq}, {e13, Relation::Eq},
        {big, Relation::Eq},
    };

    std::vector<std::pair<VarId, RealValue>> model;
    CHECK(trySquareCascade(cons, k, &model));   // the cascade constructs + validates a model
}

TEST_CASE("trySquareCascade: rational-multiple generators collapse (sqrt2 and sqrt(1/2))") {
    auto kp = createPolynomialKernel();
    PolynomialKernel& k = *kp;
    VarId a = k.getOrCreateVar("a");
    VarId b = k.getOrCreateVar("b");
    auto V = [&](VarId v) { return k.mkVar(v); };
    auto C = [&](int n) { return k.mkConst(mpq_class(n)); };

    // a^2 = 1/2  (generator sqrt(1/2));  b^2 = 2  (= 4 * 1/2, so b = 2 sqrt(1/2) = 2a);
    // the link b - 2a = 0 must validate over the SINGLE collapsed generator.
    PolyId ea = k.add(k.mul(C(2), k.pow(V(a), 2)), C(-1));   // 2 a^2 - 1
    PolyId eb = k.add(k.pow(V(b), 2), C(-2));                // b^2 - 2
    PolyId link = k.sub(V(b), k.mul(C(2), V(a)));            // b - 2 a
    std::vector<std::pair<PolyId, Relation>> cons = {
        {ea, Relation::Eq}, {eb, Relation::Eq}, {link, Relation::Eq},
        {V(a), Relation::Gt}, {V(b), Relation::Gt},
    };
    std::vector<std::pair<VarId, RealValue>> model;
    CHECK(trySquareCascade(cons, k, &model));

    // A genuinely DISTINCT second generator (sqrt(3) vs sqrt(1/2)) must NOT collapse:
    // 1/2 and 3 differ by a non-square ratio, so the cascade cannot place both in one
    // field and returns false (no false sat).
    VarId d = k.getOrCreateVar("d");
    PolyId ed = k.add(k.pow(V(d), 2), C(-3));               // d^2 - 3
    std::vector<std::pair<PolyId, Relation>> cons2 = {
        {ea, Relation::Eq}, {ed, Relation::Eq}, {V(a), Relation::Gt}, {V(d), Relation::Gt},
    };
    CHECK_FALSE(trySquareCascade(cons2, k, nullptr));
}

TEST_CASE("trySquareCascade: coupled linear subsystem (Gaussian elimination over a generator)") {
    auto kp = createPolynomialKernel();
    PolynomialKernel& k = *kp;
    VarId a = k.getOrCreateVar("a");
    VarId x = k.getOrCreateVar("x");
    VarId y = k.getOrCreateVar("y");
    auto V = [&](VarId v) { return k.mkVar(v); };
    auto C = [&](int n) { return k.mkConst(mpq_class(n)); };

    // generator a = sqrt(1/2):  2 a^2 - 1 = 0.
    PolyId ea = k.add(k.mul(C(2), k.pow(V(a), 2)), C(-1));
    // Two equations that COUPLE x and y — neither is single-variable, so the
    // single-var rationalizing derive cannot fire; only Gaussian elimination splits
    // them:  e1: x + y - 3a = 0 ;  e2: x - y - a = 0.  Solution x = 2a, y = a (both in
    // Q(sqrt 1/2)). This also exercises FLATTENING: e1 derives x = 3a - y BEFORE y is
    // known, so the stored value must be flattened to 2a once y = a is derived from e2.
    PolyId e1 = k.sub(k.add(V(x), V(y)), k.mul(C(3), V(a)));
    PolyId e2 = k.sub(k.sub(V(x), V(y)), V(a));
    std::vector<std::pair<PolyId, Relation>> cons = {
        {ea, Relation::Eq}, {e1, Relation::Eq}, {e2, Relation::Eq},
        {V(a), Relation::Gt}, {V(x), Relation::Gt}, {V(y), Relation::Gt},
    };
    std::vector<std::pair<VarId, RealValue>> model;
    CHECK(trySquareCascade(cons, k, &model));      // constructs + validates the full model
    CHECK(model.size() == 3u);                     // a, x, y all assigned

    // An INCONSISTENT third equation over the same coupled vars must be REJECTED: the
    // cascade derives x, y from e1/e2 then validates e3 over the generator and fails.
    PolyId e3 = k.sub(k.sub(V(x), V(y)), k.mul(C(5), V(a)));   // x - y - 5a = 0 (contradicts e2)
    std::vector<std::pair<PolyId, Relation>> bad = {
        {ea, Relation::Eq}, {e1, Relation::Eq}, {e2, Relation::Eq}, {e3, Relation::Eq},
        {V(a), Relation::Gt}, {V(x), Relation::Gt}, {V(y), Relation::Gt},
    };
    CHECK_FALSE(trySquareCascade(bad, k, nullptr));
}
