#include "nlcolver/Solver.h"
#include <doctest/doctest.h>
#include <fstream>
#include <filesystem>

using namespace nlcolver;

static std::string writeTempSmt2(const std::string& content) {
    std::string path = std::filesystem::temp_directory_path() / "nlcolver_test.smt2";
    std::ofstream ofs(path);
    ofs << content;
    return path;
}

TEST_CASE("Solver: sat - simple conjunction") {
    std::string path = writeTempSmt2(
        "(declare-const p Bool)\n"
        "(declare-const q Bool)\n"
        "(assert (and p q))\n"
        "(check-sat)\n"
    );

    Solver solver;
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
}

TEST_CASE("Solver: unsat - contradiction") {
    std::string path = writeTempSmt2(
        "(declare-const p Bool)\n"
        "(assert p)\n"
        "(assert (not p))\n"
        "(check-sat)\n"
    );

    Solver solver;
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("Solver: sat - 3-SAT instance") {
    std::string path = writeTempSmt2(
        "(declare-const p Bool)\n"
        "(declare-const q Bool)\n"
        "(declare-const r Bool)\n"
        "(assert (or r p q))\n"
        "(assert (or (not q) (not p)))\n"
        "(assert (or (not q) (not r)))\n"
        "(check-sat)\n"
    );

    Solver solver;
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
}

TEST_CASE("Solver: push/pop scope") {
    std::string path = writeTempSmt2(
        "(declare-const p Bool)\n"
        "(declare-const q Bool)\n"
        "(assert p)\n"
        "(check-sat)\n"
    );

    Solver solver;
    CHECK(solver.parseFile(path));
    CHECK(static_cast<int>(solver.checkSat()) == static_cast<int>(Result::Sat));

    solver.push();
    // With no new assertions, still sat
    CHECK(static_cast<int>(solver.checkSat()) == static_cast<int>(Result::Sat));

    solver.pop();
    // After pop, original assertions should still be satisfiable
    CHECK(static_cast<int>(solver.checkSat()) == static_cast<int>(Result::Sat));
}

TEST_CASE("Solver: empty assertions = sat") {
    std::string path = writeTempSmt2(
        "(declare-const p Bool)\n"
        "(check-sat)\n"
    );

    Solver solver;
    CHECK(solver.parseFile(path));
    CHECK(static_cast<int>(solver.checkSat()) == static_cast<int>(Result::Sat));
}

// ---------------------------------------------------------------------------
// P0 Safe Routing soundness regression tests
// ---------------------------------------------------------------------------

TEST_CASE("P0 Routing: Int variable without set-logic routes to LIA") {
    std::string path = writeTempSmt2(
        "(declare-const x Int)\n"
        "(assert (= (* 2 x) 1))\n"
        "(check-sat)\n"
    );
    Solver solver;
    CHECK(solver.parseFile(path));
    CHECK(static_cast<int>(solver.checkSat()) == static_cast<int>(Result::Unsat));
}

TEST_CASE("P0 Routing: Real variable without set-logic routes to LRA") {
    std::string path = writeTempSmt2(
        "(declare-const x Real)\n"
        "(assert (> x 0))\n"
        "(assert (< x 10))\n"
        "(check-sat)\n"
    );
    Solver solver;
    CHECK(solver.parseFile(path));
    CHECK(static_cast<int>(solver.checkSat()) == static_cast<int>(Result::Sat));
}

TEST_CASE("P0 Routing: QF_LRA declared with Int variable returns Unknown") {
    std::string path = writeTempSmt2(
        "(set-logic QF_LRA)\n"
        "(declare-const x Int)\n"
        "(assert (= (* 2 x) 1))\n"
        "(check-sat)\n"
    );
    Solver solver;
    solver.setLogic("QF_LRA");
    CHECK(solver.parseFile(path));
    CHECK(static_cast<int>(solver.checkSat()) == static_cast<int>(Result::Unknown));
}

TEST_CASE("P0 Routing: QF_LIA declared with Real variable returns Unknown") {
    std::string path = writeTempSmt2(
        "(set-logic QF_LIA)\n"
        "(declare-const x Real)\n"
        "(assert (> x 0))\n"
        "(assert (< x 0))\n"
        "(check-sat)\n"
    );
    Solver solver;
    solver.setLogic("QF_LIA");
    CHECK(solver.parseFile(path));
    CHECK(static_cast<int>(solver.checkSat()) == static_cast<int>(Result::Unknown));
}

TEST_CASE("P0 Routing: mixed Int/Real without set-logic returns Unknown") {
    std::string path = writeTempSmt2(
        "(declare-const x Int)\n"
        "(declare-const y Real)\n"
        "(assert (> (+ x y) 0))\n"
        "(check-sat)\n"
    );
    Solver solver;
    CHECK(solver.parseFile(path));
    CHECK(static_cast<int>(solver.checkSat()) == static_cast<int>(Result::Unknown));
}

TEST_CASE("P0 Routing: Int nonlinear without set-logic routes to NIA") {
    std::string path = writeTempSmt2(
        "(declare-const x Int)\n"
        "(assert (= (* x x) 4))\n"
        "(check-sat)\n"
    );
    Solver solver;
    CHECK(solver.parseFile(path));
    CHECK(static_cast<int>(solver.checkSat()) == static_cast<int>(Result::Sat));
}

TEST_CASE("P0 Routing: pure boolean without set-logic works") {
    std::string path = writeTempSmt2(
        "(declare-const p Bool)\n"
        "(declare-const q Bool)\n"
        "(assert (and p q))\n"
        "(check-sat)\n"
    );
    Solver solver;
    CHECK(solver.parseFile(path));
    CHECK(static_cast<int>(solver.checkSat()) == static_cast<int>(Result::Sat));
}

TEST_CASE("LRA: same-variable multiple bounds -> unsat") {
    // x >= 0  (weaker bound)
    // x >= 3  (stronger bound)
    // x <= 2  (conflicts with stronger bound)
    // The conflict must include x >= 3 and x <= 2, not x >= 0.
    std::string path = writeTempSmt2(
        "(set-logic QF_LRA)\n"
        "(declare-const x Real)\n"
        "(assert (>= x 0))\n"
        "(assert (>= x 3))\n"
        "(assert (<= x 2))\n"
        "(check-sat)\n"
    );
    Solver solver;
    CHECK(solver.parseFile(path));
    CHECK(static_cast<int>(solver.checkSat()) == static_cast<int>(Result::Unsat));
}

TEST_CASE("LRA: strict same-variable immediate conflict -> unsat") {
    // x <= 1
    // x >= 1
    // x > 1   conflicts with x <= 1
    // The conflict must include x > 1 and x <= 1.
    std::string path = writeTempSmt2(
        "(set-logic QF_LRA)\n"
        "(declare-const x Real)\n"
        "(assert (<= x 1))\n"
        "(assert (>= x 1))\n"
        "(assert (> x 1))\n"
        "(check-sat)\n"
    );
    Solver solver;
    CHECK(solver.parseFile(path));
    CHECK(static_cast<int>(solver.checkSat()) == static_cast<int>(Result::Unsat));
}
