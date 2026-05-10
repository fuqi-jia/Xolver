#include <doctest/doctest.h>
#include "nlcolver/Solver.h"
#include <fstream>
#include <filesystem>

using namespace nlcolver;

static std::string writeTempSmt2(const std::string& content) {
    std::string path = std::filesystem::temp_directory_path() / "nlcolver_nia.smt2";
    std::ofstream ofs(path);
    ofs << content;
    return path;
}

TEST_CASE("NIA: trivial constant unsat (= 1 0)") {
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(assert (= 1 0))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("NIA: trivial constant sat (> 1 0)") {
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(assert (> 1 0))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
}

TEST_CASE("NIA: non-constant returns Unknown (= (* x x) 2)") {
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
    // NIA-Core: UnivariateIntegerReasoner proves x^2=2 has no integer roots (UNSAT)
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("NIA: false literal negation (not (> 1 0)) -> unsat") {
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(assert (not (> 1 0)))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("NIA: distinct constant unsat (distinct 1 1)") {
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(assert (distinct 1 1))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("NIA: eq negation constant unsat (not (= 1 1))") {
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(assert (not (= 1 1)))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("NIA: non-integer rational constant returns Unknown") {
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(assert (= (/ 1 2) 0))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unknown));
}

TEST_CASE("NIA: linear atom goes through polynomial path -> Sat") {
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(assert (>= x 0))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    // Linear constraint x>=0 is satisfiable (e.g. x=0)
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
}

// ===========================================================================
// Category F: Strict inequality end-to-end
// ===========================================================================

TEST_CASE("NIA: strict Lt (< x 5) -> sat (x=4)") {
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(assert (< x 5))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
}

TEST_CASE("NIA: strict Gt (> x 0) -> sat (x=1)") {
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(assert (> x 0))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
}

TEST_CASE("NIA: strict Lt + Gt direct conflict (< x 3) + (> x 3) -> unsat") {
    // Normalizes to: x <= 2 and x >= 4 → direct empty-domain conflict
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(assert (< x 3))\n"
        "(assert (> x 3))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("NIA: strict nonlinear (< (* x x) 0) -> unsat") {
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

// ===========================================================================
// Category H: False literal effective relation regression
// ===========================================================================

TEST_CASE("NIA: false Leq effective relation (not (<= x 0)) + (<= x 0) -> unsat") {
    // not(x <= 0) means x > 0, which normalizes to x >= 1.
    // Together with x <= 0: direct empty-domain conflict.
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(assert (not (<= x 0)))\n"
        "(assert (<= x 0))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("NIA: false Geq effective relation (not (>= x 0)) + (>= x 0) -> unsat") {
    // not(x >= 0) means x < 0, which normalizes to x <= -1.
    // Together with x >= 0: direct empty-domain conflict.
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(assert (not (>= x 0)))\n"
        "(assert (>= x 0))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}
