// Tests for Agent-1 (linear arithmetic) flag-gated techniques:
//   ZOLVER_LRA_PIVOT_HEUR — entering-var pivot heuristic + Bland fallback.
//   ZOLVER_LIA_REPAIR      — rounding-based LRA->LIA integrality repair.
//
// Both are default-OFF and sound regardless of value. These tests confirm the
// ON path reaches the same verdicts as the OFF path (the flags must never
// change a SAT/UNSAT answer).

#include <doctest/doctest.h>
#include "zolver/Solver.h"
#include "theory/arith/lra/GeneralSimplex.h"
#include <cstdlib>
#include <fstream>
#include <filesystem>

using namespace zolver;

namespace {

std::string writeTempSmt2(const std::string& content, const std::string& tag) {
    std::string path =
        std::filesystem::temp_directory_path() / ("zolver_a1_" + tag + ".smt2");
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

TEST_CASE("ZOLVER_LRA_PIVOT_HEUR: verdict matches Bland-only path") {
    // OFF
    unsetenv("ZOLVER_LRA_PIVOT_HEUR");
    auto satOff = solveSampleLra(true);
    auto unsatOff = solveSampleLra(false);
    CHECK(satOff == GeneralSimplex::Result::Sat);
    CHECK(unsatOff == GeneralSimplex::Result::Unsat);

    // ON
    setenv("ZOLVER_LRA_PIVOT_HEUR", "1", 1);
    auto satOn = solveSampleLra(true);
    auto unsatOn = solveSampleLra(false);
    CHECK(satOn == GeneralSimplex::Result::Sat);
    CHECK(unsatOn == GeneralSimplex::Result::Unsat);
    unsetenv("ZOLVER_LRA_PIVOT_HEUR");
}

TEST_CASE("ZOLVER_LIA_REPAIR: SAT instance solved via repair") {
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
    setenv("ZOLVER_LIA_REPAIR", "1", 1);
    {
        Solver solver;
        solver.setLogic("QF_LIA");
        CHECK(solver.parseFile(path));
        Result r = solver.checkSat();
        CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
    }
    unsetenv("ZOLVER_LIA_REPAIR");
}

TEST_CASE("ZOLVER_LIA_REPAIR: UNSAT instance still UNSAT") {
    std::string path = writeTempSmt2(
        "(set-logic QF_LIA)\n"
        "(declare-const x Int)\n"
        "(assert (= (* 2 x) 1))\n"
        "(check-sat)\n",
        "repair_unsat");
    setenv("ZOLVER_LIA_REPAIR", "1", 1);
    {
        Solver solver;
        solver.setLogic("QF_LIA");
        CHECK(solver.parseFile(path));
        Result r = solver.checkSat();
        CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
    }
    unsetenv("ZOLVER_LIA_REPAIR");
}
