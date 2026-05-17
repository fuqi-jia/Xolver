#include "nlcolver/Solver.h"
#include <doctest/doctest.h>
#include <fstream>
#include <filesystem>

using namespace nlcolver;

static std::string writeTempSmt2(const std::string& content) {
    std::string path = std::filesystem::temp_directory_path() / "nlcolver_test_ite_rb.smt2";
    std::ofstream ofs(path);
    ofs << content;
    return path;
}

TEST_CASE("ITE rollback stress: push c=true -> pop -> push c=false -> pop -> push then=else -> pop") {
    std::string path = writeTempSmt2(
        "(set-logic QF_UF)\n"
        "(declare-fun c () Bool)\n"
        "(declare-fun a () Bool)\n"
        "(declare-fun b () Bool)\n"

        "(push)\n"
        "(assert (= c true))\n"
        "(assert (distinct (ite c a b) a))\n"
        "(check-sat)\n"    // unsat
        "(pop)\n"

        "(push)\n"
        "(assert (= c false))\n"
        "(assert (distinct (ite c a b) b))\n"
        "(check-sat)\n"    // unsat
        "(pop)\n"

        "(push)\n"
        "(assert (= a b))\n"
        "(assert (distinct (ite c a b) a))\n"
        "(check-sat)\n"    // unsat
        "(pop)\n"

        "(push)\n"
        "(assert (= c true))\n"
        "(assert (distinct (ite c a b) a))\n"
        "(check-sat)\n"    // unsat
        "(pop)\n"

        "(assert (= (ite c a b) (ite c a b)))\n"
        "(check-sat)\n"    // sat
    );

    Solver solver;
    CHECK(solver.parseFile(path));

    Result r1 = solver.checkSat();  // unsat
    CHECK(static_cast<int>(r1) == static_cast<int>(Result::Unsat));

    Result r2 = solver.checkSat();  // unsat
    CHECK(static_cast<int>(r2) == static_cast<int>(Result::Unsat));

    Result r3 = solver.checkSat();  // unsat
    CHECK(static_cast<int>(r3) == static_cast<int>(Result::Unsat));

    Result r4 = solver.checkSat();  // unsat
    CHECK(static_cast<int>(r4) == static_cast<int>(Result::Unsat));

    Result r5 = solver.checkSat();  // sat
    CHECK(static_cast<int>(r5) == static_cast<int>(Result::Sat));
}
