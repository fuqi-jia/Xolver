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
