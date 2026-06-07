// White-box: ProjectionClosure — the unconditionally-sound Collins projection
// composed across the variable order. Key property the legacy single-step
// projection lacked: a constraint with >=2 unassigned higher variables is
// projected ALL THE WAY down, so the lowest level gets real delineating roots
// (no whole-line fallback => no false UNSAT).

#include <doctest/doctest.h>
#include <gmpxx.h>
#include <algorithm>
#include <set>
#include <unordered_map>
#include <vector>
#include "theory/arith/nra/projection/ProjectionClosure.h"
#include "theory/arith/nra/core/CdcacCore.h"   // Feature A: reasonProjectionSubset

using namespace xolver;

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

// ---- Feature A (conflict generalization) provenance --------------------------

TEST_CASE("A1: single-input closure — every boundary descends from input 0") {
    RationalPolynomial f; f.addVar(Y, 2, 1); f.addVar(X, 1, -1); f.normalize();  // y^2 - x
    ProjectionClosure c;
    c.build({f}, {X, Y});
    for (int k = 0; k <= 1; ++k)
        for (int id : c.levelPolys(k)) {
            const auto& orig = c.inputOrigins(id);
            CHECK_FALSE(orig.empty());                 // provenance recorded
            for (int o : orig) CHECK(o == 0);          // only input f
        }
}

TEST_CASE("A1: a pairwise resultant unions BOTH input origins") {
    RationalPolynomial f; f.addVar(Y, 2, 1); f.addVar(X, 1, -1); f.normalize();  // y^2 - x
    RationalPolynomial g; g.addVar(Y, 1, 1); g.addVar(X, 1, -1); g.normalize();  // y - x
    ProjectionClosure c;
    c.build({f, g}, {X, Y});
    bool sawBoth = false;
    for (int k = 0; k <= 1; ++k)
        for (int id : c.levelPolys(k)) {
            const auto& orig = c.inputOrigins(id);
            CHECK_FALSE(orig.empty());
            for (int o : orig) CHECK((o == 0 || o == 1));   // only the two inputs
            std::set<int> s(orig.begin(), orig.end());
            if (s.count(0) && s.count(1)) sawBoth = true;
        }
    CHECK(sawBoth);   // res_y(y^2-x, y-x) = x^2-x descends from both
}

TEST_CASE("A2: reasonProjectionSubset keeps only polys whose origins are within the reasons") {
    std::unordered_map<PolyId, std::vector<int>> origins;
    origins[PolyId{10}] = {0};         // from constraint 0
    origins[PolyId{11}] = {0, 1};      // from 0 and 1
    origins[PolyId{12}] = {2};         // from 2 (NOT a reason)
    origins[PolyId{13}] = {};          // unknown provenance
    std::vector<PolyId> level = {PolyId{10}, PolyId{11}, PolyId{12}, PolyId{13}};
    auto sub = CdcacCore::reasonProjectionSubset(origins, level, {0, 1});
    auto has = [&](PolyId p) { return std::find(sub.begin(), sub.end(), p) != sub.end(); };
    CHECK(has(PolyId{10}));        // {0} ⊆ {0,1}
    CHECK(has(PolyId{11}));        // {0,1} ⊆ {0,1}
    CHECK_FALSE(has(PolyId{12}));  // {2} ⊄ {0,1}
    CHECK_FALSE(has(PolyId{13}));  // unknown provenance → excluded
    CHECK(sub.size() == 2);
}
