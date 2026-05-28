// LazardLifter — per-poly real-root placement for one CDCAC lift (step D).
// supported=true with ordered sections for the cases the oracle decides;
// supported=false (caller falls back to Collins) whenever any step is
// inconclusive or a genuine multi-poly merge is required. Never a wrong verdict.

#include <doctest/doctest.h>
#include <gmpxx.h>
#include "theory/arith/nra/valuation/LazardLifter.h"
#include "theory/arith/nra/valuation/RationalRootIsolation.h"   // countRealRootsIn

using namespace xolver;

static VarId A0 = VarId{100}, X = VarId{1};

// K = Q(sqrt2), embedding alpha = +sqrt2 in [7/5, 3/2].
static TowerContext sqrt2Ctx() {
    TowerContext ctx;
    ctx.extensionVars = {A0};
    RationalPolynomial m0; m0.addVar(A0, 2, 1); m0.addConstant(-2); m0.normalize();
    ctx.minimalPolys = {m0};
    AlgebraicRoot ar; ar.lower = mpq_class(7, 5); ar.upper = mpq_class(3, 2);
    ctx.generators = {RealAlg::fromAlgebraic(ar)};
    return ctx;
}

TEST_CASE("Lift: no polynomials => supported, single (-inf,+inf) sector") {
    auto r = lazardLift({}, X, TowerContext{});
    CHECK(r.supported);
    CHECK(r.sections.empty());
}

TEST_CASE("Lift: constant-in-x poly contributes no boundary => supported, empty") {
    RationalPolynomial F; F.addConstant(5); F.normalize();   // no X
    auto r = lazardLift({F}, X, TowerContext{});
    CHECK(r.supported);
    CHECK(r.sections.empty());
}

TEST_CASE("Lift k=0: single poly x^2-2 places two sections (+-sqrt2)") {
    RationalPolynomial F; F.addVar(X, 2, 1); F.addConstant(-2); F.normalize();
    auto r = lazardLift({F}, X, TowerContext{});
    CHECK(r.supported);
    REQUIRE(r.sections.size() == 2);
    CHECK(r.sections[0].lo < r.sections[1].lo);   // ascending, disjoint isolating brackets
    CHECK(r.sections[0].hi <= r.sections[1].lo);
    // each bracket isolates exactly one root of the defining poly
    CHECK(countRealRootsIn(r.defPoly, X, r.sections[0].lo, r.sections[0].hi) == 1);
    CHECK(countRealRootsIn(r.defPoly, X, r.sections[1].lo, r.sections[1].hi) == 1);
    // the two roots straddle 0 (-sqrt2 < 0 < +sqrt2)
    CHECK(r.sections[0].lo < mpq_class(0));
    CHECK(r.sections[1].hi > mpq_class(0));
}

TEST_CASE("Lift k=0: x^2+1 has no real roots => supported, empty") {
    RationalPolynomial F; F.addVar(X, 2, 1); F.addConstant(1); F.normalize();
    auto r = lazardLift({F}, X, TowerContext{});
    CHECK(r.supported);
    CHECK(r.sections.empty());
}

TEST_CASE("Lift over Q(sqrt2): F=x-alpha places the single section +sqrt2") {
    RationalPolynomial F; F.addVar(X, 1, 1); F.addVar(A0, 1, -1); F.normalize();   // x - A0
    auto r = lazardLift({F}, X, sqrt2Ctx());
    CHECK(r.supported);
    REQUIRE(r.sections.size() == 1);          // only +sqrt2 kept (-sqrt2 dropped)
    // the kept bracket isolates exactly one root and lies on the positive side
    CHECK(countRealRootsIn(r.defPoly, X, r.sections[0].lo, r.sections[0].hi) == 1);
    CHECK(r.sections[0].hi > mpq_class(0));
    CHECK(r.sections[0].lo >= mpq_class(0));   // excludes the negative conjugate -sqrt2
}

TEST_CASE("Lift over Q(sqrt2): F=x^2+alpha (conjugate roots) => supported, empty") {
    RationalPolynomial F; F.addVar(X, 2, 1); F.addVar(A0, 1, 1); F.normalize();   // x^2 + A0
    auto r = lazardLift({F}, X, sqrt2Ctx());
    CHECK(r.supported);
    CHECK(r.sections.empty());   // Norm x^4-2 roots are the -sqrt2 branch, dropped
}

TEST_CASE("Lift: inconclusive poly (x^2-sqrt2 needs Trager) => unsupported") {
    RationalPolynomial F; F.addVar(X, 2, 1); F.addVar(A0, 1, -1); F.normalize();   // x^2 - A0
    auto r = lazardLift({F}, X, sqrt2Ctx());
    CHECK_FALSE(r.supported);   // degree-2 proper factor => oracle Unknown => fall back
}

TEST_CASE("Lift: two polys both contributing boundaries => unsupported (merge deferred)") {
    RationalPolynomial F1; F1.addVar(X, 1, 1); F1.addConstant(-1); F1.normalize();  // x-1
    RationalPolynomial F2; F2.addVar(X, 2, 1); F2.addConstant(-2); F2.normalize();  // x^2-2
    auto r = lazardLift({F1, F2}, X, TowerContext{});
    CHECK_FALSE(r.supported);   // two contributors: cross-poly merge not yet sound
}

TEST_CASE("Lift: one poly with roots + one with none => supported (single contributor)") {
    RationalPolynomial F1; F1.addVar(X, 2, 1); F1.addConstant(1); F1.normalize();   // x^2+1 (none)
    RationalPolynomial F2; F2.addVar(X, 1, 1); F2.addConstant(-3); F2.normalize();  // x-3 (one)
    auto r = lazardLift({F1, F2}, X, TowerContext{});
    CHECK(r.supported);
    REQUIRE(r.sections.size() == 1);           // only x-3 contributes a boundary
    // the isolating bracket contains the root 3 and exactly one root of defPoly
    CHECK(r.sections[0].lo < mpq_class(3));
    CHECK(mpq_class(3) <= r.sections[0].hi);
    CHECK(countRealRootsIn(r.defPoly, X, r.sections[0].lo, r.sections[0].hi) == 1);
}
