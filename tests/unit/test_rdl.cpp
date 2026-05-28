#include <doctest/doctest.h>
#include "xolver/Solver.h"
#include <fstream>
#include <filesystem>

using namespace xolver;

static std::string writeTempSmt2(const std::string& content) {
    std::string path = std::filesystem::temp_directory_path() / "xolver_rdl_test.smt2";
    std::ofstream ofs(path);
    ofs << content;
    return path;
}

TEST_CASE("RDL: strict zero cycle UNSAT") {
    std::string path = writeTempSmt2(
        "(set-logic QF_RDL)\n"
        "(declare-const x Real)\n"
        "(declare-const y Real)\n"
        "(assert (< (- x y) 1))\n"
        "(assert (<= (- y x) -1))\n"
        "(check-sat)\n"
    );
    Solver solver;
    solver.setLogic("QF_RDL");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("RDL: strict SAT x-y<1 and y-x<=0") {
    std::string path = writeTempSmt2(
        "(set-logic QF_RDL)\n"
        "(declare-const x Real)\n"
        "(declare-const y Real)\n"
        "(assert (< (- x y) 1))\n"
        "(assert (<= (- y x) 0))\n"
        "(check-sat)\n"
    );
    Solver solver;
    solver.setLogic("QF_RDL");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
}

TEST_CASE("RDL: disequality UNSAT") {
    std::string path = writeTempSmt2(
        "(set-logic QF_RDL)\n"
        "(declare-const x Real)\n"
        "(assert (= x 0))\n"
        "(assert (not (= x 0)))\n"
        "(check-sat)\n"
    );
    Solver solver;
    solver.setLogic("QF_RDL");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("RDL: basic SAT with rational bounds") {
    std::string path = writeTempSmt2(
        "(set-logic QF_RDL)\n"
        "(declare-const x Real)\n"
        "(declare-const y Real)\n"
        "(assert (<= (- x y) (/ 5 2)))\n"
        "(assert (<= (- y x) (- (/ 3 2))))\n"
        "(check-sat)\n"
    );
    Solver solver;
    solver.setLogic("QF_RDL");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
}

TEST_CASE("RDL: Div constant strict bound") {
    std::string path = writeTempSmt2(
        "(set-logic QF_RDL)\n"
        "(declare-const x Real)\n"
        "(declare-const y Real)\n"
        "(assert (< (- x y) (/ 3 2)))\n"
        "(assert (> (- x y) (/ 1 2)))\n"
        "(check-sat)\n"
    );
    Solver solver;
    solver.setLogic("QF_RDL");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
}

TEST_CASE("RDL: non-difference atom is satisfiable via Cap. 10 fallback") {
    // `x + y <= 3` is not a difference-logic atom. The RDL theory
    // returns Unknown for the atom itself, but the validated
    // CandidateModelSearch (Cap. 10) finds a rational witness
    // (e.g. x=0, y=0) and the Solver returns Sat. This is sound: the
    // formula IS satisfiable.
    std::string path = writeTempSmt2(
        "(set-logic QF_RDL)\n"
        "(declare-const x Real)\n"
        "(declare-const y Real)\n"
        "(assert (<= (+ x y) 3))\n"
        "(check-sat)\n"
    );
    Solver solver;
    solver.setLogic("QF_RDL");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
}
