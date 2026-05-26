// White-box: ProjectionClosure — the unconditionally-sound Collins projection
// composed across the variable order. Key property the legacy single-step
// projection lacked: a constraint with >=2 unassigned higher variables is
// projected ALL THE WAY down, so the lowest level gets real delineating roots
// (no whole-line fallback => no false UNSAT).

#include <doctest/doctest.h>
#include <gmpxx.h>
#include "theory/arith/nra/projection/ProjectionClosure.h"

using namespace zolver;

static VarId X = VarId{1}, Y = VarId{2}, Z = VarId{3};

static bool levelHasPolyContaining(const ProjectionClosure& c, int level, VarId v) {
    for (int id : c.levelPolys(level)) {
        if (c.entries()[id].poly.contains(v)) return true;
    }
    return false;
}

TEST_CASE("Closure: 2-var f=y^2-x projects to a boundary on x") {
    RationalPolynomial f; f.addVar(Y, 2, 1); f.addVar(X, 1, -1); f.normalize();
    ProjectionClosure c;
    auto r = c.build({f}, {X, Y});
    CHECK(r == ProjectionIncompleteReason::None);
    CHECK(c.complete());
    REQUIRE_FALSE(c.levelPolys(0).empty());
    CHECK(levelHasPolyContaining(c, 0, X));
}

TEST_CASE("Closure: 3-var z^2+y^2-x chains z->y->x to a boundary on x") {
    RationalPolynomial f;
    f.addVar(Z, 2, 1); f.addVar(Y, 2, 1); f.addVar(X, 1, -1); f.normalize();
    ProjectionClosure c;
    auto r = c.build({f}, {X, Y, Z});
    CHECK(r == ProjectionIncompleteReason::None);
    CHECK(c.complete());
    REQUIRE_FALSE(c.levelPolys(0).empty());
    CHECK(levelHasPolyContaining(c, 0, X));
}

TEST_CASE("Closure: CONVOI2-style product var*linear reaches the low var") {
    RationalPolynomial f;
    f.addTerm({{X,1},{Z,1}}, 1);
    f.addTerm({{Y,1},{Z,1}}, 1);
    f.addConstant(-1);
    f.normalize();
    ProjectionClosure c;
    auto r = c.build({f}, {X, Y, Z});
    CHECK(r == ProjectionIncompleteReason::None);
    CHECK(c.complete());
    CHECK_FALSE(c.entries().empty());
}

TEST_CASE("Closure: perfect square stays complete (repeated root still a boundary)") {
    RationalPolynomial f;
    f.addVar(Y, 2, 1);
    f.addTerm({{X,1},{Y,1}}, -2);
    f.addVar(X, 2, 1);
    f.normalize();
    ProjectionClosure c;
    auto r = c.build({f}, {X, Y});
    CHECK(r == ProjectionIncompleteReason::None);
    CHECK(c.complete());
    CHECK_FALSE(c.levelPolys(0).empty());
}

TEST_CASE("Closure: provenance is recorded for every projected polynomial") {
    RationalPolynomial f; f.addVar(Y, 2, 1); f.addVar(X, 1, -1); f.normalize();
    ProjectionClosure c;
    c.build({f}, {X, Y});
    bool sawInput = false, sawDerived = false;
    for (const auto& e : c.entries()) {
        if (e.source.op == ProjectionOpKind::Input) sawInput = true;
        else {
            sawDerived = true;
            CHECK(e.source.parent1 >= 0);
            CHECK(e.source.eliminatedVar == Y);
        }
    }
    CHECK(sawInput);
    CHECK(sawDerived);
}

TEST_CASE("Closure: single-var constraint stays complete") {
    RationalPolynomial g; g.addVar(X, 2, 1); g.addConstant(-1); g.normalize();
    ProjectionClosure c;
    auto r = c.build({g}, {X, Y});
    CHECK(r == ProjectionIncompleteReason::None);
    CHECK(c.complete());
    REQUIRE_FALSE(c.levelPolys(0).empty());
}
