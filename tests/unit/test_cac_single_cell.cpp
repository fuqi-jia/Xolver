// CAC single-cell projection (module B — characterize). Verifies the Lazard
// projection is split correctly into this-level boundary polys (contain elimVar)
// vs the downward characterization (free of elimVar), matching known cells.

#include <doctest/doctest.h>
#include <gmpxx.h>
#include "theory/arith/nra/cac/SingleCellProjection.h"

using namespace xolver;

static const VarId VX = VarId{1}, VY = VarId{2};

static RationalPolynomial konst(long c) { return RationalPolynomial::fromConstant(mpq_class(c)); }

// y^2 - x
static RationalPolynomial yy_minus_x() {
    RationalPolynomial p; p.addVar(VY, 2, 1); p.addVar(VX, 1, -1); p.normalize(); return p;
}
// x^2 + y^2 - 1
static RationalPolynomial circle() {
    RationalPolynomial p; p.addVar(VX, 2, 1); p.addVar(VY, 2, 1);
    p = p + konst(-1); p.normalize(); return p;
}

static bool hasPolyInXOnly(const std::vector<RationalPolynomial>& v) {
    for (const auto& p : v) if (p.degree(VY) == 0 && p.degree(VX) >= 1) return true;
    return false;
}

TEST_CASE("characterize: y^2 - x eliminate y") {
    auto r = characterize({yy_minus_x()}, VY);
    CHECK(r.complete);
    // The squarefree factor y^2 - x stays in y as this level's boundary.
    REQUIRE(r.boundaryPolys.size() >= 1);
    for (const auto& p : r.boundaryPolys) CHECK(p.degree(VY) >= 1);
    // The discriminant / trailing coeff (~ x) is the downward boundary.
    CHECK(hasPolyInXOnly(r.downwardPolys));
    for (const auto& p : r.downwardPolys) CHECK(p.degree(VY) == 0);
}

TEST_CASE("characterize: circle x^2 + y^2 - 1 eliminate y") {
    auto r = characterize({circle()}, VY);
    CHECK(r.complete);
    REQUIRE(r.boundaryPolys.size() >= 1);
    // Discriminant in y is ~ (1 - x^2): a downward poly in x only.
    CHECK(hasPolyInXOnly(r.downwardPolys));
}

TEST_CASE("characterize: resultant of two lines in y") {
    // y - x and y - 2 : res_y = (x - 2), a downward poly in x only.
    RationalPolynomial a; a.addVar(VY, 1, 1); a.addVar(VX, 1, -1); a.normalize();   // y - x
    RationalPolynomial b; b.addVar(VY, 1, 1); b = b + konst(-2); b.normalize();     // y - 2
    auto r = characterize({a, b}, VY);
    CHECK(r.complete);
    CHECK(hasPolyInXOnly(r.downwardPolys));
}

TEST_CASE("characterize: empty input is complete and empty") {
    auto r = characterize({}, VY);
    CHECK(r.complete);
    CHECK(r.boundaryPolys.empty());
    CHECK(r.downwardPolys.empty());
}

TEST_CASE("characterize: no constants leak into either bucket") {
    auto r = characterize({circle()}, VY);
    for (const auto& p : r.boundaryPolys) CHECK_FALSE(p.isConstant());
    for (const auto& p : r.downwardPolys) CHECK_FALSE(p.isConstant());
}
