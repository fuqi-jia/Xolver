#include <doctest/doctest.h>
#include "xolver/Solver.h"
#include <filesystem>
#include <fstream>

using namespace xolver;

#define CHECK_RESULT(actual, expected) \
    CHECK(static_cast<int>(actual) == static_cast<int>(expected))

static std::string writeSmt2(const std::string& name, const std::string& body) {
    auto p = std::filesystem::temp_directory_path() / ("xolver_lin_" + name + ".smt2");
    std::ofstream(p) << body;
    return p.string();
}

// These tests exercise IncrementalLinearizer (McCormick + square cuts) and the
// ICP engine indirectly through NRA/NIA formulae. They are black-box: if the
// linearizer or ICP is broken, the answer will degrade from sat/unsat to
// unknown or, worse, become unsound — the framework will then flag it.

TEST_CASE("Linearizer: square cut on x^2 = 4 finds integer solution") {
    auto path = writeSmt2("sq_cut_sat",
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(assert (= (* x x) 4))\n"
        "(check-sat)\n");
    Solver s;
    REQUIRE(s.parseFile(path));
    CHECK_RESULT(s.checkSat(), Result::Sat);
}

TEST_CASE("Linearizer: McCormick on bounded x*y refutes unsat case") {
    // x,y ∈ [0,1] so x*y ∈ [0,1]; asserting x*y > 2 is unsat.
    auto path = writeSmt2("mccormick_unsat",
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(declare-const y Int)\n"
        "(assert (>= x 0)) (assert (<= x 1))\n"
        "(assert (>= y 0)) (assert (<= y 1))\n"
        "(assert (> (* x y) 2))\n"
        "(check-sat)\n");
    Solver s;
    REQUIRE(s.parseFile(path));
    CHECK_RESULT(s.checkSat(), Result::Unsat);
}

TEST_CASE("Linearizer: x^2 = -1 always unsat via positivity") {
    auto path = writeSmt2("x2_neg",
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(assert (= (* x x) (- 1)))\n"
        "(check-sat)\n");
    Solver s;
    REQUIRE(s.parseFile(path));
    CHECK_RESULT(s.checkSat(), Result::Unsat);
}

TEST_CASE("ICP-style: contracting interval finds tight bounds") {
    // x ∈ [0, 100] with x*x = 4 should contract to x = 2.
    auto path = writeSmt2("icp_contract_sat",
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(assert (>= x 0))\n"
        "(assert (<= x 100))\n"
        "(assert (= (* x x) 4))\n"
        "(check-sat)\n");
    Solver s;
    REQUIRE(s.parseFile(path));
    CHECK_RESULT(s.checkSat(), Result::Sat);
}

TEST_CASE("Linearizer: refutes large coefficient infeasibility") {
    auto path = writeSmt2("large_coeff",
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(assert (>= x 1)) (assert (<= x 5))\n"
        "(assert (> (* 1000 x) 100000))\n"
        "(check-sat)\n");
    Solver s;
    REQUIRE(s.parseFile(path));
    CHECK_RESULT(s.checkSat(), Result::Unsat);
}

TEST_CASE("ICP: open interval x*x < 1 with x > 0 is sat") {
    auto path = writeSmt2("icp_open",
        "(set-logic QF_NRA)\n"
        "(declare-const x Real)\n"
        "(assert (> x 0))\n"
        "(assert (< (* x x) 1))\n"
        "(check-sat)\n");
    Solver s;
    REQUIRE(s.parseFile(path));
    CHECK_RESULT(s.checkSat(), Result::Sat);
}
