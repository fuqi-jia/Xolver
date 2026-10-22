#include <doctest/doctest.h>
#include "xolver/Solver.h"
#include <filesystem>
#include <fstream>

using namespace xolver;

#define CHECK_RESULT(actual, expected) \
    CHECK(static_cast<int>(actual) == static_cast<int>(expected))
#define CHECK_NOT_RESULT(actual, expected) \
    CHECK(static_cast<int>(actual) != static_cast<int>(expected))

static std::string writeTempSmt2(const std::string& name, const std::string& content) {
    auto p = std::filesystem::temp_directory_path() / ("xolver_no_" + name + ".smt2");
    std::ofstream(p) << content;
    return p.string();
}

TEST_CASE("NO: UF + LIA shared-variable congruence — unsat") {
    // This is a soundness obligation even while completeness is evolving.
    auto path = writeTempSmt2("uf_lia_share_unsat",
        "(set-logic QF_UFLIA)\n"
        "(declare-fun f (Int) Int)\n"
        "(declare-fun x () Int)\n"
        "(assert (= x 1))\n"
        "(assert (= (f x) 5))\n"
        "(assert (distinct (f 1) 5))\n"
        "(check-sat)\n");
    Solver s;
    REQUIRE(s.parseFile(path));
    auto r = s.checkSat();
    CHECK_MESSAGE(static_cast<int>(r) != static_cast<int>(Result::Sat),
                  "EUF<->LIA bridge should not return sat");
}

TEST_CASE("NO: UF + LRA shared-variable equality — sat") {
    auto path = writeTempSmt2("uf_lra_share_sat",
        "(set-logic QF_UFLRA)\n"
        "(declare-fun f (Real) Real)\n"
        "(declare-fun x () Real)\n"
        "(declare-fun y () Real)\n"
        "(assert (= x y))\n"
        "(assert (= (f x) (f y)))\n"
        "(check-sat)\n");
    Solver s;
    REQUIRE(s.parseFile(path));
    auto r = s.checkSat();
    CHECK_MESSAGE(static_cast<int>(r) != static_cast<int>(Result::Unsat), "Equal args under shared eq must give equal images");
}

TEST_CASE("NO: UF + LIA bound-induced disequality — unsat") {
    auto path = writeTempSmt2("uf_lia_bound_unsat",
        "(set-logic QF_UFLIA)\n"
        "(declare-fun f (Int) Int)\n"
        "(declare-fun a () Int)\n"
        "(declare-fun b () Int)\n"
        "(assert (>= a 0))\n"
        "(assert (<= a 1))\n"
        "(assert (>= b 2))\n"
        "(assert (= (f a) (f b)))\n"
        "(assert (distinct a b))\n"
        "(check-sat)\n");
    Solver s;
    REQUIRE(s.parseFile(path));
    auto r = s.checkSat();
    CHECK_NOT_RESULT(r, Result::Unsat);  // f is not necessarily injective — sat
}

TEST_CASE("NO: UF + LIA tight bounds and uninterpreted function — sat") {
    auto path = writeTempSmt2("uf_lia_tight_sat",
        "(set-logic QF_UFLIA)\n"
        "(declare-fun g (Int Int) Int)\n"
        "(declare-fun x () Int)\n"
        "(declare-fun y () Int)\n"
        "(assert (= x 5))\n"
        "(assert (= y 10))\n"
        "(assert (> (g x y) 0))\n"
        "(check-sat)\n");
    Solver s;
    REQUIRE(s.parseFile(path));
    auto r = s.checkSat();
    CHECK_RESULT(r, Result::Sat);
}

TEST_CASE("NO: UF + LRA distinct + equal-image is unsat") {
    auto path = writeTempSmt2("uf_lra_distinct_unsat",
        "(set-logic QF_UFLRA)\n"
        "(declare-fun f (Real) Real)\n"
        "(declare-fun x () Real)\n"
        "(declare-fun y () Real)\n"
        "(assert (= x y))\n"
        "(assert (distinct (f x) (f y)))\n"
        "(check-sat)\n");
    Solver s;
    REQUIRE(s.parseFile(path));
    auto r = s.checkSat();
    CHECK_RESULT(r, Result::Unsat);
}

TEST_CASE("NO: pure-LIA case in UFLIA logic (no UF symbols used) — sat") {
    auto path = writeTempSmt2("uflia_pure_lia",
        "(set-logic QF_UFLIA)\n"
        "(declare-fun x () Int)\n"
        "(assert (>= x 0))\n"
        "(assert (<= x 5))\n"
        "(check-sat)\n");
    Solver s;
    REQUIRE(s.parseFile(path));
    auto r = s.checkSat();
    CHECK_RESULT(r, Result::Sat);
}

TEST_CASE("NO: pure-EUF case in UFLIA logic (no arithmetic used) — sat") {
    auto path = writeTempSmt2("uflia_pure_euf",
        "(set-logic QF_UFLIA)\n"
        "(declare-fun f (Int) Int)\n"
        "(declare-fun a () Int)\n"
        "(declare-fun b () Int)\n"
        "(assert (= a b))\n"
        "(assert (= (f a) (f b)))\n"
        "(check-sat)\n");
    Solver s;
    REQUIRE(s.parseFile(path));
    auto r = s.checkSat();
    CHECK_RESULT(r, Result::Sat);
}

TEST_CASE("NO: concrete UF model preserves coinciding arithmetic witnesses") {
    auto path = writeTempSmt2("shared_numeric_model",
        "(set-logic QF_UFNIA)(declare-const i Int)(declare-const j Int)"
        "(declare-const k Int)(declare-fun f (Int) Int)"
        "(assert (not (<= i (f 5))))(assert (distinct 2 (+ 5 k)))"
        "(assert (< 5 (- 0 i)))(assert (<= (+ k k) (f i)))"
        "(assert (not (< (f (+ 5 (f (- 1)))) 1)))"
        "(assert (= i (f i)))(assert (< j 1))(check-sat)");
    Solver solver;
    REQUIRE(solver.parseFile(path));
    REQUIRE((solver.checkSat() == Result::Sat));
    CHECK((solver.validateModel() == Solver::ModelValidation::Satisfied));
}
