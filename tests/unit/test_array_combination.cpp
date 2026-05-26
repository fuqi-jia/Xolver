// Array + arithmetic (+ UF) combination logics: QF_ALIA / QF_ALRA /
// QF_AUFLIA / QF_AUFLRA.
//
// These exercise Nelson-Oppen combination where array index/element terms are
// arithmetic and shared with the LIA/LRA solver (and, for AUF*, with UF). The
// key soundness path is Row2 over ARITH indices: the (i=j) antecedent must be
// a shared-equality atom observed by BOTH arith and EUF, so an arith fact like
// (= i (+ j 0)) drives the Row2 case split. Verdicts cross-checked vs z3+cvc5.

#include "nlcolver/Solver.h"
#include <doctest/doctest.h>
#include <fstream>
#include <filesystem>

using namespace nlcolver;

static std::string writeComboSmt2(const std::string& content) {
    static int counter = 0;
    std::string path = std::filesystem::temp_directory_path() /
        ("nlcolver_array_combo_test_" + std::to_string(counter++) + ".smt2");
    std::ofstream ofs(path);
    ofs << content;
    return path;
}

static Result solveStr(const std::string& smt) {
    std::string path = writeComboSmt2(smt);
    Solver solver;
    REQUIRE(solver.parseFile(path));
    return solver.checkSat();
}

TEST_SUITE("array_combination") {

// ---- Row2 driven by an ARITH index equality -----------------------------

TEST_CASE("QF_ALIA Row2 unsat: arith fact i=j+0 forces select(store)=v") {
    Result r = solveStr(
        "(set-logic QF_ALIA)\n"
        "(declare-const a (Array Int Int))\n"
        "(declare-const i Int)\n"
        "(declare-const j Int)\n"
        "(declare-const v Int)\n"
        "(assert (= i (+ j 0)))\n"
        "(assert (not (= (select (store a i v) j) v)))\n"
        "(check-sat)\n");
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("QF_ALRA Row2 unsat: arith fact over reals drives Row2") {
    Result r = solveStr(
        "(set-logic QF_ALRA)\n"
        "(declare-const a (Array Real Real))\n"
        "(declare-const i Real)\n"
        "(declare-const j Real)\n"
        "(declare-const v Real)\n"
        "(assert (= i (+ j 0.0)))\n"
        "(assert (not (= (select (store a i v) j) v)))\n"
        "(check-sat)\n");
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

// ---- Read value coupled to arithmetic ------------------------------------

TEST_CASE("QF_ALIA unsat: select value used in arithmetic contradiction") {
    Result r = solveStr(
        "(set-logic QF_ALIA)\n"
        "(declare-const a (Array Int Int))\n"
        "(declare-const i Int)\n"
        "(assert (= (select a i) 3))\n"
        "(assert (> (select a i) 5))\n"
        "(check-sat)\n");
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("QF_ALIA unsat: store value coupled to arith variable") {
    Result r = solveStr(
        "(set-logic QF_ALIA)\n"
        "(declare-const a (Array Int Int))\n"
        "(declare-const i Int)\n"
        "(declare-const x Int)\n"
        "(assert (= (select (store a i 7) i) x))\n"
        "(assert (not (= x 7)))\n"
        "(check-sat)\n");
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

// ---- Arrays + UF over reads ----------------------------------------------

TEST_CASE("QF_AUFLIA unsat: UF over array read respects Row1") {
    Result r = solveStr(
        "(set-logic QF_AUFLIA)\n"
        "(declare-fun f (Int) Int)\n"
        "(declare-const a (Array Int Int))\n"
        "(declare-const i Int)\n"
        "(declare-const v Int)\n"
        "(assert (not (= (f (select (store a i v) i)) (f v))))\n"
        "(check-sat)\n");
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("QF_AUFLRA unsat: UF + select value in arith") {
    Result r = solveStr(
        "(set-logic QF_AUFLRA)\n"
        "(declare-fun f (Real) Real)\n"
        "(declare-const a (Array Real Real))\n"
        "(declare-const i Real)\n"
        "(assert (= (select a i) (f i)))\n"
        "(assert (= (f i) 3.0))\n"
        "(assert (> (select a i) 5.0))\n"
        "(check-sat)\n");
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

// ---- Genuinely satisfiable cases (validated models / sound Unknown) ------

TEST_CASE("QF_ALIA sat: arith index disequality + read fall-through") {
    Result r = solveStr(
        "(set-logic QF_ALIA)\n"
        "(declare-const a (Array Int Int))\n"
        "(declare-const i Int)\n"
        "(declare-const j Int)\n"
        "(declare-const v Int)\n"
        "(assert (not (= i j)))\n"
        "(assert (= (select (store a i v) j) (select a j)))\n"
        "(check-sat)\n");
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
}

TEST_CASE("QF_ALIA sat: stored value read back, index bounded") {
    Result r = solveStr(
        "(set-logic QF_ALIA)\n"
        "(declare-const a (Array Int Int))\n"
        "(declare-const i Int)\n"
        "(assert (= (select (store a i 5) i) 5))\n"
        "(assert (> i 0))\n"
        "(assert (< i 10))\n"
        "(check-sat)\n");
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
}

}  // TEST_SUITE
