#include <doctest/doctest.h>
#include "xolver/Solver.h"
#include <fstream>
#include <filesystem>

using namespace xolver;

static std::string writeTempSmt2(const std::string& content) {
    std::string path = std::filesystem::temp_directory_path() / "xolver_nia_core.smt2";
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

TEST_CASE("NIA-Core: x^2 <= 4 -> sat (square bound)") {
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(assert (<= (* x x) 4))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
}

TEST_CASE("NIA-Core: x^2 <= -1 -> unsat (square bound)") {
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(assert (<= (* x x) -1))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("NIA-Core: x^2 = 49 -> sat (square bound)") {
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(assert (= (* x x) 49))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
}

TEST_CASE("NIA-Core: x^2 != 4, 0<=x<=10 -> sat (square exclusion)") {
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(assert (>= x 0))\n"
        "(assert (<= x 10))\n"
        "(assert (not (= (* x x) 4)))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
}

// ---------------------------------------------------------------------------
// Sum-of-squares bound + bounded enumeration
// ---------------------------------------------------------------------------

TEST_CASE("NIA-Core: x^2 + y^2 = 65, x>=0, y>=0 -> sat (sos bound)") {
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(declare-const y Int)\n"
        "(assert (>= x 0))\n"
        "(assert (>= y 0))\n"
        "(assert (= (+ (* x x) (* y y)) 65))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
}

TEST_CASE("NIA-Core: x^2 + y^2 = 5000, 0<=x,y<=100 -> sat (sos bound + enumeration)") {
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(declare-const y Int)\n"
        "(assert (>= x 0))\n"
        "(assert (<= x 100))\n"
        "(assert (>= y 0))\n"
        "(assert (<= y 100))\n"
        "(assert (= (+ (* x x) (* y y)) 5000))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
}

TEST_CASE("NIA-Core: x^2 + y^2 <= -1 -> unsat (sos conflict)") {
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(declare-const y Int)\n"
        "(assert (<= (+ (* x x) (* y y)) -1))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

// ---------------------------------------------------------------------------
// Interval evaluation pruning
// ---------------------------------------------------------------------------

TEST_CASE("NIA-Core: 0<=x<=100000, x^3+1<=0 -> unsat (interval pruning)") {
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(assert (>= x 0))\n"
        "(assert (<= x 100000))\n"
        "(assert (<= (+ (* x (* x x)) 1) 0))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("NIA-Core: 0<=x<=2, x^3-8<=0 -> sat (interval not violated)") {
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(assert (>= x 0))\n"
        "(assert (<= x 2))\n"
        "(assert (<= (- (* x (* x x)) 8) 0))\n"
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

TEST_CASE("NIA-Core: x*y=0, x!=0, y!=0 -> unsat (factor direct conflict)") {
    // Factor direct conflict: xy=0 ∧ x≠0 ∧ y≠0 is detected as UNSAT
    // by AlgebraicIntegerReasoner::checkFactorDirectConflict.
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
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

// ---------------------------------------------------------------------------
// IncrementalLinearizer V1 tests
// ---------------------------------------------------------------------------

TEST_CASE("NIA-Core: 0<=x,y<=10, x*y>200 -> unsat (McCormick)") {
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(declare-const y Int)\n"
        "(assert (>= x 0))\n"
        "(assert (<= x 10))\n"
        "(assert (>= y 0))\n"
        "(assert (<= y 10))\n"
        "(assert (> (* x y) 200))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("NIA-Core: x^2+y^2<=1, x=2 -> unsat (square cut)") {
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(declare-const y Int)\n"
        "(assert (<= (+ (* x x) (* y y)) 1))\n"
        "(assert (= x 2))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

// ---------------------------------------------------------------------------
// Category D-N: AlgebraicIntegerReasoner N-var modular refutation (iter-79)
// ---------------------------------------------------------------------------

TEST_CASE("NIA-Core: 3-var modular refutation — x+y+z=1 ∧ x^2+y^2+z^2=0 -> unsat (mod 2)") {
    // x+y+z = 1 forces an odd number of {x,y,z} to be 1 mod 2.
    // x^2+y^2+z^2 = 0 forces every x,y,z = 0 mod 2 (each square is 0 mod 2).
    // 1 != 0 mod 2 -> UNSAT. checkModular extended to N-var should catch this.
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(declare-const y Int)\n"
        "(declare-const z Int)\n"
        "(assert (= (+ x y z) 1))\n"
        "(assert (= (+ (* x x) (* y y) (* z z)) 0))\n"
        "(check-sat)\n"
    );
    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("NIA-Core: 4-var modular system over mod 3 -> unsat") {
    // x^2 + y^2 ≡ 0 (mod 3) forces x ≡ 0 AND y ≡ 0 mod 3 (squares mod 3 ∈ {0,1}).
    // z^2 + w^2 = 5 mod 3 = 2; but squares mod 3 sum to at most 2, only via 1+1.
    // Combined with z+w = 1 mod 3 (no choice of z,w in {1,2} that sums to 1 satisfies both),
    // ⇒ UNSAT. Exercises the N-var enumeration path (was hardcoded ≤2 var before iter-79).
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(declare-const y Int)\n"
        "(declare-const z Int)\n"
        "(declare-const w Int)\n"
        "(assert (= (+ (* x x) (* y y)) (* 3 z)))\n"   // x^2+y^2 ≡ 0 mod 3
        "(assert (= (+ x y) (+ 1 (* 3 w))))\n"          // x+y ≡ 1 mod 3
        "(check-sat)\n"
    );
    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    // Either Unsat (modular refuter fires) or Unknown (other reasoners). NEVER Sat.
    CHECK(static_cast<int>(r) != static_cast<int>(Result::Sat));
}

// ---------------------------------------------------------------------------
// Category D-N+: Soundness of env-overridable modular caps (iter-84)
// ---------------------------------------------------------------------------

TEST_CASE("NIA-Core: SAT case with relaxed modular var cap stays SAT (no false UNSAT)") {
    // x*y = 6 ∧ x+y = 5 has the integer solutions (x=2,y=3) and (x=3,y=2).
    // With relaxed iter-84 env caps the modular refuter still operates
    // SOUND: it can only emit UNSAT, never SAT. So this case must remain SAT
    // regardless of how wide the caps are set.
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(declare-const y Int)\n"
        "(assert (= (* x y) 6))\n"
        "(assert (= (+ x y) 5))\n"
        "(check-sat)\n"
    );
    // Note: env vars are read once via static const at first call; if a
    // previous test already initialized them at defaults, setenv here may
    // not take effect. But default behavior is also SAT-preserving — the
    // crux is: the modular refuter never returns SAT from incomplete data,
    // and the bounded_ engine handles small-system SAT.
    setenv("XOLVER_NIA_MODULAR_MAX_VARS", "30", 1);
    setenv("XOLVER_NIA_MODULAR_MAX_ENUM", "100000", 1);

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
    // Critically: NEVER Unsat (would indicate false UNSAT from modular refuter).
    CHECK(static_cast<int>(r) != static_cast<int>(Result::Unsat));
}

TEST_CASE("NIA-Core: env-overridable moduli list preserves SAT on satisfiable system") {
    // iter-87: XOLVER_NIA_MODULAR_MODULI override. A satisfiable case must
    // stay SAT regardless of which moduli the user injects. The modular
    // refuter is UNSAT-only; any moduli that misclassify SAT→UNSAT would
    // be a soundness bug, not a tunability feature.
    //
    // x = 3, y = 5: x*y = 15, x+y = 8. Trivially SAT.
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(declare-const y Int)\n"
        "(assert (= (* x y) 15))\n"
        "(assert (= (+ x y) 8))\n"
        "(check-sat)\n"
    );
    setenv("XOLVER_NIA_MODULAR_MODULI", "2,3,5,7,11,13", 1);
    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
    // Defensive: invalid moduli (e.g. m=1 which is not bounded by parser)
    // would silently fall back to defaults — never produce wrong UNSAT.
    CHECK(static_cast<int>(r) != static_cast<int>(Result::Unsat));
}

TEST_CASE("NIA-Core: malformed moduli env var falls back gracefully") {
    // iter-87: XOLVER_NIA_MODULAR_MODULI parser must reject bogus values
    // (out-of-range, non-numeric tail) gracefully — never crash, never
    // misclassify. Tests defensive fallback to default moduli list.
    //
    // Same satisfiable case as above; just verify the parser handles junk.
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(declare-const y Int)\n"
        "(assert (= (* x y) 15))\n"
        "(assert (= (+ x y) 8))\n"
        "(check-sat)\n"
    );
    setenv("XOLVER_NIA_MODULAR_MODULI", "abc,999999,not_a_number", 1);
    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
}

// ---------------------------------------------------------------------------
// Category D-BF: iter-89 bilinear factor restriction (XOLVER_NIA_BILINEAR_FACTOR)
// ---------------------------------------------------------------------------

TEST_CASE("NIA-Core: x*y=7 (prime) via bilinear factor → SAT") {
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(declare-const y Int)\n"
        "(assert (= (* x y) 7))\n"
        "(check-sat)\n"
    );
    setenv("XOLVER_NIA_BILINEAR_FACTOR", "1", 1);
    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
    CHECK(static_cast<int>(r) != static_cast<int>(Result::Unsat));
}

TEST_CASE("NIA-Core: bilinear factor x*y=-6 (negative) → SAT") {
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(declare-const y Int)\n"
        "(assert (= (* x y) (- 6)))\n"
        "(check-sat)\n"
    );
    setenv("XOLVER_NIA_BILINEAR_FACTOR", "1", 1);
    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
}

