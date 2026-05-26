#include <doctest/doctest.h>
#include "zolver/Solver.h"
#include <fstream>
#include <filesystem>

using namespace zolver;

static std::string writeTempSmt2(const std::string& content) {
    std::string path = std::filesystem::temp_directory_path() / "zolver_cdclt.smt2";
    std::ofstream ofs(path);
    ofs << content;
    return path;
}

TEST_CASE("CDCL(T): boolean + LRA unsat") {
    std::string path = writeTempSmt2(
        "(declare-const p Bool)\n"
        "(declare-const x Real)\n"
        "(assert (or p (> x 0)))\n"
        "(assert (or (not p) (< x 0)))\n"
        "(assert (= x 0))\n"
        "(check-sat)\n"
    );

    Solver solver;
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("CDCL(T): boolean + LRA sat") {
    std::string path = writeTempSmt2(
        "(declare-const p Bool)\n"
        "(declare-const x Real)\n"
        "(assert (or p (> x 0)))\n"
        "(assert (or (not p) (< x 0)))\n"
        "(check-sat)\n"
    );

    Solver solver;
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
}
