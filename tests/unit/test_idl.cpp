#include <doctest/doctest.h>
#include "xolver/Solver.h"
#include <fstream>
#include <filesystem>

using namespace xolver;

static std::string writeTempSmt2(const std::string& content) {
    std::string path = std::filesystem::temp_directory_path() / "xolver_idl_test.smt2";
    std::ofstream ofs(path);
    ofs << content;
    return path;
}

TEST_CASE("IDL: basic SAT x-y<=3 and y-x<=2") {
    std::string path = writeTempSmt2(
        "(set-logic QF_IDL)\n"
        "(declare-const x Int)\n"
        "(declare-const y Int)\n"
        "(assert (<= (- x y) 3))\n"
        "(assert (<= (- y x) 2))\n"
        "(check-sat)\n"
    );
    Solver solver;
    solver.setLogic("QF_IDL");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
}

TEST_CASE("IDL: negative cycle UNSAT") {
    std::string path = writeTempSmt2(
        "(set-logic QF_IDL)\n"
        "(declare-const x Int)\n"
        "(declare-const y Int)\n"
        "(declare-const z Int)\n"
        "(assert (<= (- x y) 3))\n"
        "(assert (<= (- y z) 4))\n"
        "(assert (<= (- z x) -8))\n"
        "(check-sat)\n"
    );
    Solver solver;
    solver.setLogic("QF_IDL");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("IDL: strict contradiction UNSAT") {
    std::string path = writeTempSmt2(
        "(set-logic QF_IDL)\n"
        "(declare-const x Int)\n"
        "(declare-const y Int)\n"
        "(assert (< (- x y) 3))\n"
        "(assert (>= (- x y) 3))\n"
        "(check-sat)\n"
    );
    Solver solver;
    solver.setLogic("QF_IDL");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("IDL: disequality UNSAT") {
    std::string path = writeTempSmt2(
        "(set-logic QF_IDL)\n"
        "(declare-const x Int)\n"
        "(declare-const y Int)\n"
        "(assert (= x y))\n"
        "(assert (not (= x y)))\n"
        "(check-sat)\n"
    );
    Solver solver;
    solver.setLogic("QF_IDL");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("IDL: single variable bounds SAT") {
    std::string path = writeTempSmt2(
        "(set-logic QF_IDL)\n"
        "(declare-const x Int)\n"
        "(assert (<= x 5))\n"
        "(assert (>= x 3))\n"
        "(check-sat)\n"
    );
    Solver solver;
    solver.setLogic("QF_IDL");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
}

TEST_CASE("IDL: non-difference atom is satisfiable via Cap. 10 fallback") {
    // `x + y <= 3` is not a difference-logic atom (it has two unknowns on
    // one side instead of a difference). The IDL theory returns Unknown
    // for the atom itself, but the validated CandidateModelSearch
    // (Cap. 10) finds an integer witness — e.g. (x=0, y=0) — and the
    // Solver returns Sat. This is sound: the formula IS satisfiable.
    std::string path = writeTempSmt2(
        "(set-logic QF_IDL)\n"
        "(declare-const x Int)\n"
        "(declare-const y Int)\n"
        "(assert (<= (+ x y) 3))\n"
        "(check-sat)\n"
    );
    Solver solver;
    solver.setLogic("QF_IDL");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
}

TEST_CASE("IDL: equality with non-integer RHS is UNSAT") {
    std::string path = writeTempSmt2(
        "(set-logic QF_IDL)\n"
        "(declare-const x Int)\n"
        "(declare-const y Int)\n"
        "(assert (= (- x y) (/ 1 2)))\n"
        "(check-sat)\n"
    );
    Solver solver;
    solver.setLogic("QF_IDL");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("IDL: Div constant rational bound is parsed correctly") {
    std::string path = writeTempSmt2(
        "(set-logic QF_IDL)\n"
        "(declare-const x Int)\n"
        "(declare-const y Int)\n"
        "(assert (<= (- x y) (/ 5 2)))\n"
        "(assert (>= (- x y) (/ 3 2)))\n"
        "(check-sat)\n"
    );
    Solver solver;
    solver.setLogic("QF_IDL");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
}
