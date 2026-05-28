#include "xolver/Solver.h"
#include <doctest/doctest.h>
#include <fstream>
#include <filesystem>

using namespace xolver;

static std::string writeTempSmt2(const std::string& content) {
    std::string path = std::filesystem::temp_directory_path() / "xolver_test_ite.smt2";
    std::ofstream ofs(path);
    ofs << content;
    return path;
}

TEST_CASE("ITE R1: ite(true, a, b) = a -> sat") {
    std::string path = writeTempSmt2(
        "(set-logic QF_UF)\n"
        "(declare-fun a () Bool)\n"
        "(declare-fun b () Bool)\n"
        "(assert (= (ite true a b) a))\n"
        "(check-sat)\n"
    );
    Solver solver;
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
}

TEST_CASE("ITE R2: ite(false, a, b) = b -> sat") {
    std::string path = writeTempSmt2(
        "(set-logic QF_UF)\n"
        "(declare-fun a () Bool)\n"
        "(declare-fun b () Bool)\n"
        "(assert (= (ite false a b) b))\n"
        "(check-sat)\n"
    );
    Solver solver;
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
}

TEST_CASE("ITE R3: a=b -> ite(c, a, b) = a -> sat") {
    std::string path = writeTempSmt2(
        "(set-logic QF_UF)\n"
        "(declare-fun c () Bool)\n"
        "(declare-fun a () Bool)\n"
        "(declare-fun b () Bool)\n"
        "(assert (= a b))\n"
        "(assert (= (ite c a b) a))\n"
        "(check-sat)\n"
    );
    Solver solver;
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
}

TEST_CASE("ITE conflict: distinct(ite(c,a,b), a) /\ c=true -> unsat") {
    std::string path = writeTempSmt2(
        "(set-logic QF_UF)\n"
        "(declare-fun c () Bool)\n"
        "(declare-fun a () Bool)\n"
        "(declare-fun b () Bool)\n"
        "(assert (= c true))\n"
        "(assert (distinct (ite c a b) a))\n"
        "(check-sat)\n"
    );
    Solver solver;
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("ITE branches-equal conflict: distinct(ite(c,a,b), a) /\ a=b -> unsat") {
    std::string path = writeTempSmt2(
        "(set-logic QF_UF)\n"
        "(declare-fun c () Bool)\n"
        "(declare-fun a () Bool)\n"
        "(declare-fun b () Bool)\n"
        "(assert (= a b))\n"
        "(assert (distinct (ite c a b) a))\n"
        "(check-sat)\n"
    );
    Solver solver;
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("ITE nested: ite(c1, ite(c2,a,b), b) = b -> sat") {
    std::string path = writeTempSmt2(
        "(set-logic QF_UF)\n"
        "(declare-fun c1 () Bool)\n"
        "(declare-fun c2 () Bool)\n"
        "(declare-fun a () Bool)\n"
        "(declare-fun b () Bool)\n"
        "(assert (= (ite c1 (ite c2 a b) b) b))\n"
        "(check-sat)\n"
    );
    Solver solver;
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
}

TEST_CASE("ITE rollback opposite branch -> unsat") {
    std::string path = writeTempSmt2(
        "(set-logic QF_UF)\n"
        "(declare-fun c () Bool)\n"
        "(declare-fun a () Bool)\n"
        "(declare-fun b () Bool)\n"
        "(push)\n"
        "(assert (= c true))\n"
        "(assert (distinct (ite c a b) a))\n"
        "(check-sat)\n"
        "(pop)\n"
        "(assert (= c false))\n"
        "(assert (distinct (ite c a b) b))\n"
        "(check-sat)\n"
    );
    Solver solver;
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("ITE delayed cond merge: c=true -> sat") {
    std::string path = writeTempSmt2(
        "(set-logic QF_UF)\n"
        "(declare-fun c () Bool)\n"
        "(declare-fun a () Bool)\n"
        "(declare-fun b () Bool)\n"
        "(assert (= c true))\n"
        "(assert (= (ite c a b) a))\n"
        "(check-sat)\n"
    );
    Solver solver;
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
}

TEST_CASE("ITE delayed branch equality: a=b -> sat") {
    std::string path = writeTempSmt2(
        "(set-logic QF_UF)\n"
        "(declare-fun c () Bool)\n"
        "(declare-fun a () Bool)\n"
        "(declare-fun b () Bool)\n"
        "(assert (= a b))\n"
        "(assert (= (ite c a b) a))\n"
        "(check-sat)\n"
    );
    Solver solver;
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
}
