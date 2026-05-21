#include <doctest/doctest.h>
#include "nlcolver/Solver.h"
#include <filesystem>
#include <fstream>

using namespace nlcolver;

#define CHECK_RESULT(actual, expected) \
    CHECK(static_cast<int>(actual) == static_cast<int>(expected))

static std::string writeSmt2(const std::string& name, const std::string& body) {
    auto p = std::filesystem::temp_directory_path() / ("nlcolver_cdclt_" + name + ".smt2");
    std::ofstream(p) << body;
    return p.string();
}

TEST_CASE("CDCL(T) loop: boolean branch forces theory conflict") {
    // p=true forces x>0, but combined with x<0 — theory conflict on p=true branch.
    // p=false forces x<5, with x>10 — theory conflict on p=false branch.
    // Both branches conflict ⇒ unsat. Exercises decision/backtrack with T-conflicts.
    auto path = writeSmt2("branch_conflict",
        "(set-logic QF_LRA)\n"
        "(declare-const p Bool)\n"
        "(declare-const x Real)\n"
        "(assert (or (and p (> x 0)) (and (not p) (< x 5))))\n"
        "(assert (or (and p (< x 0)) (and (not p) (> x 10))))\n"
        "(check-sat)\n");
    Solver s;
    REQUIRE(s.parseFile(path));
    CHECK_RESULT(s.checkSat(), Result::Unsat);
}

TEST_CASE("CDCL(T) loop: T-propagation guides SAT to assignment") {
    auto path = writeSmt2("t_prop_sat",
        "(set-logic QF_LIA)\n"
        "(declare-const x Int)\n"
        "(declare-const y Int)\n"
        "(assert (or (= x 1) (= x 2)))\n"
        "(assert (= y (+ x 1)))\n"
        "(assert (or (= y 2) (= y 3)))\n"
        "(check-sat)\n");
    Solver s;
    REQUIRE(s.parseFile(path));
    CHECK_RESULT(s.checkSat(), Result::Sat);
}

TEST_CASE("CDCL(T) loop: deep backtrack after theory lemma") {
    auto path = writeSmt2("deep_backtrack",
        "(set-logic QF_LRA)\n"
        "(declare-const p1 Bool)\n"
        "(declare-const p2 Bool)\n"
        "(declare-const p3 Bool)\n"
        "(declare-const x Real)\n"
        "(assert (or p1 p2 p3))\n"
        "(assert (=> p1 (> x 100)))\n"
        "(assert (=> p2 (> x 100)))\n"
        "(assert (=> p3 (> x 100)))\n"
        "(assert (< x 0))\n"
        "(check-sat)\n");
    Solver s;
    REQUIRE(s.parseFile(path));
    CHECK_RESULT(s.checkSat(), Result::Unsat);
}

TEST_CASE("CDCL(T) loop: push/pop preserves theory state") {
    auto path = writeSmt2("push_pop",
        "(set-logic QF_LIA)\n"
        "(declare-const x Int)\n"
        "(assert (>= x 0))\n"
        "(push 1)\n"
        "(assert (<= x 5))\n"
        "(check-sat)\n"
        "(pop 1)\n"
        "(assert (<= x 100))\n"
        "(check-sat)\n");
    Solver s;
    REQUIRE(s.parseFile(path));
    // Both check-sats should be sat.
    auto r = s.checkSat();
    CHECK_RESULT(r, Result::Sat);
}

TEST_CASE("CDCL(T) loop: ITE expansion preserves soundness") {
    auto path = writeSmt2("ite_sound",
        "(set-logic QF_LRA)\n"
        "(declare-const c Bool)\n"
        "(declare-const x Real)\n"
        "(assert (= (ite c x (- x)) 5))\n"
        "(check-sat)\n");
    Solver s;
    REQUIRE(s.parseFile(path));
    CHECK_RESULT(s.checkSat(), Result::Sat);
}

TEST_CASE("CDCL(T) loop: incremental reset clears state") {
    Solver s;
    auto p1 = writeSmt2("inc_1",
        "(set-logic QF_LRA)\n"
        "(declare-const x Real)\n"
        "(assert (> x 0))\n"
        "(check-sat)\n");
    REQUIRE(s.parseFile(p1));
    CHECK_RESULT(s.checkSat(), Result::Sat);

    s.reset();
    auto p2 = writeSmt2("inc_2",
        "(set-logic QF_LRA)\n"
        "(declare-const y Real)\n"
        "(assert (> y 0))\n"
        "(assert (< y 0))\n"
        "(check-sat)\n");
    REQUIRE(s.parseFile(p2));
    CHECK_RESULT(s.checkSat(), Result::Unsat);
}
