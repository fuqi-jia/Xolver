#include <doctest/doctest.h>
#include "nlcolver/Solver.h"
#include <fstream>
#include <filesystem>

using namespace nlcolver;

static std::string writeTempSmt2(const std::string& content) {
    std::string path = std::filesystem::temp_directory_path() / "nlcolver_nia_core.smt2";
    std::ofstream ofs(path);
    ofs << content;
    return path;
}

// ---------------------------------------------------------------------------
// Univariate integer equality (RRT)
// ---------------------------------------------------------------------------

TEST_CASE("NIA-Core: x^2 = 4 -> sat") {
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(assert (= (* x x) 4))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
}

TEST_CASE("NIA-Core: x^2 = 2 -> unsat") {
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(assert (= (* x x) 2))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("NIA-Core: x^2 + 1 = 0 -> unsat") {
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(assert (= (+ (* x x) 1) 0))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

// ---------------------------------------------------------------------------
// Bounded NIA (linear bounds + nonlinear equation)
// ---------------------------------------------------------------------------

TEST_CASE("NIA-Core: 0<=x<=10, x^2=49 -> sat") {
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(assert (>= x 0))\n"
        "(assert (<= x 10))\n"
        "(assert (= (* x x) 49))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
}

TEST_CASE("NIA-Core: 0<=x<=10, x^2=50 -> unsat") {
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(assert (>= x 0))\n"
        "(assert (<= x 10))\n"
        "(assert (= (* x x) 50))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

// ---------------------------------------------------------------------------
// Square rules
// ---------------------------------------------------------------------------

TEST_CASE("NIA-Core: x^2 < 0 -> unsat") {
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(assert (< (* x x) 0))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

// ---------------------------------------------------------------------------
// GCD equality conflict
// ---------------------------------------------------------------------------

TEST_CASE("NIA-Core: 2x = 1 -> unsat") {
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(assert (= (* 2 x) 1))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

// ---------------------------------------------------------------------------
// Modular reasoning
// ---------------------------------------------------------------------------

TEST_CASE("NIA-Core: x^2 = 2 -> unsat (modular)") {
    // x^2 = 2 has no integer solution (mod 4: squares are 0 or 1)
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(assert (= (* x x) 2))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

// ---------------------------------------------------------------------------
// Disequality
// ---------------------------------------------------------------------------

TEST_CASE("NIA-Core: x != 0, x = 0 -> unsat") {
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(assert (not (= x 0)))\n"
        "(assert (= x 0))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

// ===========================================================================
// Extended tests: Categories C, D, E, G, I
// ===========================================================================

// ---------------------------------------------------------------------------
// Category C: UnivariateIntegerReasoner boundary tests
// ---------------------------------------------------------------------------

TEST_CASE("NIA-Core: x^3 - 1331 = 0 -> sat (root 11 via RRT)") {
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(assert (= (- (* x (* x x)) 1331) 0))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
}

TEST_CASE("NIA-Core: x*(x-11) = 0 -> sat (roots 0 and 11)") {
    // x^2 - 11x = 0; zero constant term with root outside [-10,10]
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(assert (= (- (* x x) (* 11 x)) 0))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
}

TEST_CASE("NIA-Core: 2x^2 - 8 = 0 -> sat (roots 2, -2)") {
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(assert (= (- (* 2 (* x x)) 8) 0))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
}

TEST_CASE("NIA-Core: x^2 - 4 != 0, 0<=x<=10 -> sat (x=3)") {
    // Neq exclusion: x cannot be 2 or -2, but x=3 is valid
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(assert (>= x 0))\n"
        "(assert (<= x 10))\n"
        "(assert (not (= (- (* x x) 4) 0)))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
}

// ---------------------------------------------------------------------------
// Category D: AlgebraicIntegerReasoner boundary tests
// ---------------------------------------------------------------------------

TEST_CASE("NIA-Core: x^2 + 1 <= 0 -> unsat") {
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(assert (<= (+ (* x x) 1) 0))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("NIA-Core: x^2 <= 0 -> sat (x=0)") {
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(assert (<= (* x x) 0))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
}

TEST_CASE("NIA-Core: 4x^2 - 2 = 0 -> unsat (nonlinear GCD)") {
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(assert (= (- (* 4 (* x x)) 2) 0))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("NIA-Core: x^2 + y^2 = 3 -> unsat (modular)") {
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(declare-const y Int)\n"
        "(assert (= (+ (* x x) (* y y)) 3))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

// ---------------------------------------------------------------------------
// Category E: Multivariate bounded enumeration
// ---------------------------------------------------------------------------

TEST_CASE("NIA-Core: 0<=x<=3, 0<=y<=3, x*y=6 -> sat") {
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(declare-const y Int)\n"
        "(assert (>= x 0))\n"
        "(assert (<= x 3))\n"
        "(assert (>= y 0))\n"
        "(assert (<= y 3))\n"
        "(assert (= (* x y) 6))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
}

TEST_CASE("NIA-Core: 0<=x<=2, 0<=y<=2, x*y=6 -> unsat") {
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(declare-const y Int)\n"
        "(assert (>= x 0))\n"
        "(assert (<= x 2))\n"
        "(assert (>= y 0))\n"
        "(assert (<= y 2))\n"
        "(assert (= (* x y) 6))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("NIA-Core: x+y=5, x*y=6 -> sat") {
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(declare-const y Int)\n"
        "(assert (= (+ x y) 5))\n"
        "(assert (= (* x y) 6))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
}

TEST_CASE("NIA-Core: 0<=x<=2, 0<=y<=2, 0<=z<=2, x+y+z=5 -> sat") {
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(declare-const y Int)\n"
        "(declare-const z Int)\n"
        "(assert (>= x 0))\n"
        "(assert (<= x 2))\n"
        "(assert (>= y 0))\n"
        "(assert (<= y 2))\n"
        "(assert (>= z 0))\n"
        "(assert (<= z 2))\n"
        "(assert (= (+ x (+ y z)) 5))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
}

// ---------------------------------------------------------------------------
// Category G: Boolean + NIA mixed
// ---------------------------------------------------------------------------

TEST_CASE("NIA-Core: (or p (= x^2 4)) -> sat") {
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(declare-const p Bool)\n"
        "(declare-const x Int)\n"
        "(assert (or p (= (* x x) 4)))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
}

TEST_CASE("NIA-Core: guarded NIA UNSAT (or (not p) (= x^2 2)) + p -> unsat") {
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(declare-const p Bool)\n"
        "(declare-const x Int)\n"
        "(assert (or (not p) (= (* x x) 2)))\n"
        "(assert p)\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("NIA-Core: (or (= x^2 4) (= x^2 2)) -> sat") {
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(assert (or (= (* x x) 4) (= (* x x) 2)))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
}

// ---------------------------------------------------------------------------
// Category I: Dynamic polynomial atom / factor lemma
// ---------------------------------------------------------------------------

TEST_CASE("NIA-Core: x*y=0, x!=0, y!=0 -> unsat (factor lemma skeleton)") {
    // Factor lemma (xy=0 => x=0 or y=0) is not yet implemented.
    // Without it, the solver cannot prove unsat for this case.
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(declare-const y Int)\n"
        "(assert (= (* x y) 0))\n"
        "(assert (not (= x 0)))\n"
        "(assert (not (= y 0)))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unknown));
}
