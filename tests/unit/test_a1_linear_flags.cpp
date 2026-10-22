// Semantic regressions for bounded heuristic pivoting and integrality repair.

#include <doctest/doctest.h>
#include "xolver/Solver.h"
#include "search/lra/GeneralSimplex.h"
#include <cstdlib>
#include <fstream>
#include <filesystem>

using namespace xolver;

namespace {

std::string writeTempSmt2(const std::string& content, const std::string& tag) {
    std::string path =
        std::filesystem::temp_directory_path() / ("xolver_a1_" + tag + ".smt2");
    std::ofstream ofs(path);
    ofs << content;
    return path;
}

// Build a small feasible / infeasible LRA system and return the simplex verdict.
// The system has enough rows that a non-trivial pivot sequence is exercised.
GeneralSimplex::Result solveSampleLra(bool feasible) {
    GeneralSimplex gs;
    int x = gs.addVar("x");
    int y = gs.addVar("y");
    int z = gs.addVar("z");
    // s1 = x + y + z, s2 = x - y, s3 = y - z
    int s1 = gs.addConstraint({{x, 1}, {y, 1}, {z, 1}}, 0);
    int s2 = gs.addConstraint({{x, 1}, {y, -1}}, 0);
    int s3 = gs.addConstraint({{y, 1}, {z, -1}}, 0);

    auto lo = [&](int v, long c) {
        gs.assertLower(v, BoundInfo(BoundValue(DeltaRational(mpq_class(c))), SatLit{(SatVar)(v + 1), true}));
    };
    auto up = [&](int v, long c) {
        gs.assertUpper(v, BoundInfo(BoundValue(DeltaRational(mpq_class(c))), SatLit{(SatVar)(v + 1), false}));
    };

    lo(s2, -1); up(s2, 1);     // -1 <= x - y <= 1
    lo(s3, -1); up(s3, 1);     // -1 <= y - z <= 1
    up(x, 5); lo(x, -5);
    up(y, 5); lo(y, -5);
    up(z, 5); lo(z, -5);
    if (feasible) {
        lo(s1, 2); up(s1, 9);  // 2 <= x+y+z <= 9 : satisfiable
    } else {
        lo(s1, 30);            // x+y+z >= 30 but each var <= 5 : infeasible
    }
    return gs.check();
}

} // namespace

TEST_CASE("Simplex pivot: feasible and infeasible systems") {
    CHECK(solveSampleLra(true) == GeneralSimplex::Result::Sat);
    CHECK(solveSampleLra(false) == GeneralSimplex::Result::Unsat);
}

TEST_CASE("Integrality repair: SAT instance solved via repair") {
    // LRA relaxation is fractional (x=2.5, y=3.5); round-to-nearest gives the
    // feasible integer point (x=3, y=4), so repair short-cuts branching.
    std::string path = writeTempSmt2(
        "(set-logic QF_LIA)\n"
        "(declare-const x Int)\n"
        "(declare-const y Int)\n"
        "(assert (>= (* 2 x) 5))\n"
        "(assert (>= (* 2 y) 7))\n"
        "(assert (<= x 100))\n"
        "(assert (<= y 100))\n"
        "(assert (<= (+ x y) 50))\n"
        "(check-sat)\n",
        "repair_sat");
    {
        Solver solver;
        solver.setLogic("QF_LIA");
        CHECK(solver.parseFile(path));
        Result r = solver.checkSat();
        CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
    }
}

TEST_CASE("Integrality repair: UNSAT instance still UNSAT") {
    std::string path = writeTempSmt2(
        "(set-logic QF_LIA)\n"
        "(declare-const x Int)\n"
        "(assert (= (* 2 x) 1))\n"
        "(check-sat)\n",
        "repair_unsat");
    {
        Solver solver;
        solver.setLogic("QF_LIA");
        CHECK(solver.parseFile(path));
        Result r = solver.checkSat();
        CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
    }
}
