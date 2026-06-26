// Step A.2: Lazard projection operator + closure (pure algebra, sample-
// independent). Soundness anchors: LC/TC/discriminant/resultant values match
// known answers; the closure composes top-down, buckets by level, dedups
// proportional polys, and reports incompleteness on budget overflow.

#include <doctest/doctest.h>
#include <gmpxx.h>
#include "theory/arith/logics/nra/projection/LazardProjectionOperator.h"
#include "theory/arith/logics/nra/projection/LazardProjectionClosure.h"

using namespace xolver;

static VarId VX = VarId{1}, VY = VarId{2}, VZ = VarId{3};

static RationalPolynomial monic(RationalPolynomial p) {
    p.normalize();
    if (p.isZero()) return p;
    mpq_class lead = p.terms().rbegin()->second;
    if (lead != 0 && lead != 1) { p *= (mpq_class(1) / lead); p.normalize(); }
    return p;
}
static bool sameUpToUnit(const RationalPolynomial& a, const RationalPolynomial& b) {
    return monic(a).terms() == monic(b).terms();
}
static const LazardItem* find(const LazardOpResult& r, LazardProjectionOpKind op) {
    for (const auto& it : r.items) if (it.op == op) return &it;
    return nullptr;
}
static int countOp(const LazardOpResult& r, LazardProjectionOpKind op) {
    int n = 0;
    for (const auto& it : r.items) if (it.op == op) ++n;
    return n;
}

// ---- Operator math --------------------------------------------------------

TEST_CASE("Lazard op: y^2 - x eliminate y => LC=1, TC=-x, disc~x, no content") {
    RationalPolynomial p; p.addVar(VY, 2, 1); p.addVar(VX, 1, -1); p.normalize();
    auto r = lazardProjectStep({p}, VY);
    CHECK(r.complete);
    CHECK(countOp(r, LazardProjectionOpKind::Content) == 0);     // content is 1
    const LazardItem* lc = find(r, LazardProjectionOpKind::LeadingCoefficient);
    REQUIRE(lc); CHECK(lc->poly.isConstant()); CHECK(lc->poly.constantValue() == 1);
    const LazardItem* tc = find(r, LazardProjectionOpKind::TrailingCoefficient);
    REQUIRE(tc);
    RationalPolynomial x; x.addVar(VX, 1, 1); x.normalize();
    CHECK(sameUpToUnit(tc->poly, x));
    const LazardItem* d = find(r, LazardProjectionOpKind::Discriminant);
    REQUIRE(d); CHECK(sameUpToUnit(d->poly, x));   // disc = -4x ~ x
}

TEST_CASE("Lazard op: x*y + x eliminate y => content=x, factor y+1") {
    RationalPolynomial p; p.addTerm({{VX, 1}, {VY, 1}}, 1); p.addVar(VX, 1, 1); p.normalize();
    auto r = lazardProjectStep({p}, VY);
    CHECK(r.complete);
    const LazardItem* c = find(r, LazardProjectionOpKind::Content);
    REQUIRE(c);
    RationalPolynomial x; x.addVar(VX, 1, 1); x.normalize();
    CHECK(sameUpToUnit(c->poly, x));
    const LazardItem* f = find(r, LazardProjectionOpKind::SquarefreeFactor);
    REQUIRE(f);
    RationalPolynomial yp1; yp1.addVar(VY, 1, 1); yp1.addConstant(1); yp1.normalize();
    CHECK(sameUpToUnit(f->poly, yp1));
    CHECK(countOp(r, LazardProjectionOpKind::Discriminant) == 0);  // linear has none
}

TEST_CASE("Lazard op: pairwise resultant res_y(y^2-x, y-1) ~ x-1") {
    RationalPolynomial p; p.addVar(VY, 2, 1); p.addVar(VX, 1, -1); p.normalize();
    RationalPolynomial q; q.addVar(VY, 1, 1); q.addConstant(-1); q.normalize();
    auto r = lazardProjectStep({p, q}, VY);
    CHECK(r.complete);
    const LazardItem* res = find(r, LazardProjectionOpKind::Resultant);
    REQUIRE(res);
    RationalPolynomial xm1; xm1.addVar(VX, 1, 1); xm1.addConstant(-1); xm1.normalize();  // x-1
    CHECK(sameUpToUnit(res->poly, xm1));
}

TEST_CASE("Lazard op: x*y - 1 eliminate y => LC=x boundary (hyperbola x=0)") {
    RationalPolynomial p; p.addTerm({{VX, 1}, {VY, 1}}, 1); p.addConstant(-1); p.normalize();
    auto r = lazardProjectStep({p}, VY);
    CHECK(r.complete);
    const LazardItem* lc = find(r, LazardProjectionOpKind::LeadingCoefficient);
    REQUIRE(lc);
    RationalPolynomial x; x.addVar(VX, 1, 1); x.normalize();
    CHECK(sameUpToUnit(lc->poly, x));
}

// ---- Closure --------------------------------------------------------------

TEST_CASE("Lazard closure: {y^2 - x} over [x,y] => x-boundary, complete") {
    RationalPolynomial p; p.addVar(VY, 2, 1); p.addVar(VX, 1, -1); p.normalize();
    LazardProjectionClosure cl;
    auto reason = cl.build({p}, {VX, VY});
    CHECK(reason == LazardIncompleteReason::None);
    CHECK(cl.complete());
    // level 1 (y) keeps y^2-x; level 0 (x) has the single boundary x (TC -x and
    // disc -4x both canonicalize to x and dedup to ONE entry).
    REQUIRE(cl.levelPolys(0).size() == 1);
    RationalPolynomial x; x.addVar(VX, 1, 1); x.normalize();
    CHECK(sameUpToUnit(cl.entries()[cl.levelPolys(0)[0]].poly, x));
    CHECK(cl.levelPolys(1).size() >= 1);
}

TEST_CASE("Lazard closure: 3-var chain z^2 + y^2 - x over [x,y,z] is complete") {
    RationalPolynomial p; p.addVar(VZ, 2, 1); p.addVar(VY, 2, 1); p.addVar(VX, 1, -1);
    p.normalize();
    LazardProjectionClosure cl;
    auto reason = cl.build({p}, {VX, VY, VZ});
    CHECK(reason == LazardIncompleteReason::None);
    CHECK(cl.complete());
    // Eliminating z then y must leave a non-empty x-level boundary (x>=0 region).
    CHECK(cl.levelPolys(0).size() >= 1);
    CHECK(cl.levelPolys(2).size() >= 1);   // z-level keeps the input
}

TEST_CASE("Lazard closure: provenance source recorded with op + eliminatedVar") {
    RationalPolynomial p; p.addVar(VY, 2, 1); p.addVar(VX, 1, -1); p.normalize();
    LazardProjectionClosure cl;
    cl.build({p}, {VX, VY});
    bool sawProjected = false;
    for (const auto& e : cl.entries()) {
        if (e.source.op != LazardProjectionOpKind::Input) {
            sawProjected = true;
            CHECK(e.source.eliminatedVar == VY);
            CHECK(e.source.parent1 >= 0);   // parent resolved to an entry index
        }
    }
    CHECK(sawProjected);
}

TEST_CASE("Lazard closure: budget overflow => incomplete (no UNSAT may rest)") {
    RationalPolynomial p; p.addVar(VY, 2, 1); p.addVar(VX, 1, -1); p.normalize();
    LazardProjectionClosure cl;
    LazardProjectionClosure::Config cfg;
    cfg.maxMatrixDim = 2;   // disc of a quadratic needs a 3x3 Sylvester submatrix
    auto reason = cl.build({p}, {VX, VY}, cfg);
    CHECK(reason == LazardIncompleteReason::ProjectionBudgetExceeded);
    CHECK_FALSE(cl.complete());
}

TEST_CASE("Lazard closure: linear-only {x + y} over [x,y] complete, no spurious boundary") {
    RationalPolynomial p; p.addVar(VX, 1, 1); p.addVar(VY, 1, 1); p.normalize();
    LazardProjectionClosure cl;
    auto reason = cl.build({p}, {VX, VY});
    CHECK(reason == LazardIncompleteReason::None);
    // x+y eliminate y: factor x+y (deg1), LC=1, TC=x. TC x is the only x-boundary.
    REQUIRE(cl.levelPolys(0).size() == 1);
    RationalPolynomial x; x.addVar(VX, 1, 1); x.normalize();
    CHECK(sameUpToUnit(cl.entries()[cl.levelPolys(0)[0]].poly, x));
}
