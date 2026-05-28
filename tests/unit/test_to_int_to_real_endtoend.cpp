#include <doctest/doctest.h>
#include "xolver/Solver.h"
#include "expr/Smt2Dumper.h"
#include <fstream>
#include <filesystem>
#include <iostream>

using namespace xolver;

static std::string writeTempSmt2(const std::string& content) {
    auto path = std::filesystem::temp_directory_path() / "test_to_int.smt2";
    std::ofstream ofs(path);
    ofs << content;
    return path.string();
}

static int resultCode(Result r) {
    switch (r) {
        case Result::Sat:     return 0;
        case Result::Unsat:   return 1;
        case Result::Unknown: return 2;
        default:              return -1;
    }
}

TEST_CASE("End-to-end: to_int linear Real variable = sat") {
    Solver solver;
    std::string smt2 = R"(
(set-logic QF_LIRA)
(declare-const x Real)
(assert (= (to_int x) 3))
(assert (= x (/ 7 2)))
(check-sat)
)";
    auto path = writeTempSmt2(smt2);
    REQUIRE(solver.parseFile(path));
    solver.dumpSMT2(std::cerr);
    auto result = solver.checkSat();
    REQUIRE(resultCode(result) == resultCode(Result::Sat));
}

TEST_CASE("End-to-end: to_int linear Real variable = unsat") {
    Solver solver;
    std::string smt2 = R"(
(set-logic QF_LIRA)
(declare-const x Real)
(assert (= (to_int x) 3))
(assert (>= x 4))
(check-sat)
)";
    auto path = writeTempSmt2(smt2);
    REQUIRE(solver.parseFile(path));
    auto result = solver.checkSat();
    REQUIRE(resultCode(result) == resultCode(Result::Unsat));
}

TEST_CASE("End-to-end: to_int nonlinear = sat (Cap. 8c lowers nonlinear to_int)") {
    // (= (to_int (* x x)) 3) means 3 <= x*x < 4, so x = sqrt(3) works.
    // ToIntDefinitionalLowerer (Cap. 8c) introduces a bridge r_t = x*x and
    // upgrades the logic from QF_LIRA to QF_NIRA so NRA-CDCAC can solve it.
    Solver solver;
    std::string smt2 = R"(
(set-logic QF_LIRA)
(declare-const x Real)
(assert (= (to_int (* x x)) 3))
(check-sat)
)";
    auto path = writeTempSmt2(smt2);
    REQUIRE(solver.parseFile(path));
    auto result = solver.checkSat();
    REQUIRE(resultCode(result) == resultCode(Result::Sat));
}

TEST_CASE("End-to-end: to_int negative floor") {
    Solver solver;
    std::string smt2 = R"(
(set-logic QF_LIRA)
(declare-const x Real)
(assert (= (to_int x) -2))
(assert (= x (- (/ 6 5))))
(check-sat)
)";
    auto path = writeTempSmt2(smt2);
    REQUIRE(solver.parseFile(path));
    auto result = solver.checkSat();
    REQUIRE(resultCode(result) == resultCode(Result::Sat));
}
