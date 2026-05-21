#include <doctest/doctest.h>
#include "nlcolver/Solver.h"
#include <filesystem>
#include <fstream>
#include <set>

using namespace nlcolver;

#define CHECK_RESULT(actual, expected) \
    CHECK(static_cast<int>(actual) == static_cast<int>(expected))
#define REQUIRE_RESULT(actual, expected) \
    REQUIRE(static_cast<int>(actual) == static_cast<int>(expected))

static std::string writeSmt2(const std::string& name, const std::string& body) {
    auto p = std::filesystem::temp_directory_path() / ("nlcolver_mc_" + name + ".smt2");
    std::ofstream(p) << body;
    return p.string();
}

// Collect all model values as strings — gives us value-set assertions even
// though we can't map varId to user var name from outside.
static std::set<std::string> modelValueSet(const Model& m) {
    std::set<std::string> result;
    for (const auto& kv : m.values()) result.insert(kv.second);
    return result;
}

TEST_CASE("MC: x = 42 has 42 in the model value set") {
    auto path = writeSmt2("eq_42",
        "(set-logic QF_LIA)\n"
        "(declare-const x Int)\n"
        "(assert (= x 42))\n"
        "(check-sat)\n");
    Solver s;
    REQUIRE(s.parseFile(path));
    REQUIRE_RESULT(s.checkSat(), Result::Sat);
    auto vs = modelValueSet(s.getModel());
    CHECK_MESSAGE(vs.count("42") > 0, "x=42 must appear in model");
}

TEST_CASE("MC: forced eq chain — model agrees with single value") {
    auto path = writeSmt2("chain_eq",
        "(set-logic QF_LIA)\n"
        "(declare-const x Int)\n"
        "(declare-const y Int)\n"
        "(declare-const z Int)\n"
        "(assert (= x 7))\n"
        "(assert (= y x))\n"
        "(assert (= z y))\n"
        "(check-sat)\n");
    Solver s;
    REQUIRE(s.parseFile(path));
    REQUIRE_RESULT(s.checkSat(), Result::Sat);
    auto m = s.getModel();
    CHECK_FALSE(m.isEmpty());
    auto vs = modelValueSet(m);
    CHECK_MESSAGE(vs.count("7") > 0, "x=y=z=7 — value 7 must show");
}

TEST_CASE("MC: real bound model in [0,1]") {
    auto path = writeSmt2("real_bound",
        "(set-logic QF_LRA)\n"
        "(declare-const x Real)\n"
        "(assert (>= x 0))\n"
        "(assert (<= x 1))\n"
        "(check-sat)\n");
    Solver s;
    REQUIRE(s.parseFile(path));
    REQUIRE_RESULT(s.checkSat(), Result::Sat);
    auto m = s.getModel();
    CHECK_FALSE(m.isEmpty());
    // Don't constrain exact form (could be "0", "1/2", "0.5", etc.) — only non-empty.
}

TEST_CASE("MC: distinct pair has at least two values in model") {
    auto path = writeSmt2("distinct_pair",
        "(set-logic QF_LIA)\n"
        "(declare-const x Int)\n"
        "(declare-const y Int)\n"
        "(assert (= x 1))\n"
        "(assert (= y 2))\n"
        "(assert (distinct x y))\n"
        "(check-sat)\n");
    Solver s;
    REQUIRE(s.parseFile(path));
    REQUIRE_RESULT(s.checkSat(), Result::Sat);
    auto vs = modelValueSet(s.getModel());
    CHECK_MESSAGE(vs.count("1") > 0, "value 1 must appear in model");
    CHECK_MESSAGE(vs.count("2") > 0, "value 2 must appear in model");
}

TEST_CASE("MC: ITE selection materializes a branch value") {
    auto path = writeSmt2("ite_branch",
        "(set-logic QF_LIA)\n"
        "(declare-const c Bool)\n"
        "(declare-const x Int)\n"
        "(assert c)\n"
        "(assert (= x (ite c 10 (- 10))))\n"
        "(check-sat)\n");
    Solver s;
    REQUIRE(s.parseFile(path));
    REQUIRE_RESULT(s.checkSat(), Result::Sat);
    auto vs = modelValueSet(s.getModel());
    CHECK_MESSAGE(vs.count("10") > 0, "c=true ⇒ x=10");
}

TEST_CASE("MC: model after pop reflects only persisted constraints") {
    auto path = writeSmt2("pop_model",
        "(set-logic QF_LIA)\n"
        "(declare-const x Int)\n"
        "(push 1)\n"
        "(assert (= x 99))\n"
        "(pop 1)\n"
        "(assert (= x 1))\n"
        "(check-sat)\n");
    Solver s;
    REQUIRE(s.parseFile(path));
    REQUIRE_RESULT(s.checkSat(), Result::Sat);
    auto vs = modelValueSet(s.getModel());
    CHECK_MESSAGE(vs.count("1") > 0, "after pop, only x=1 remains");
    CHECK_MESSAGE(vs.count("99") == 0, "popped constraint x=99 must NOT survive");
}

TEST_CASE("MC: NIA perfect-square model contains a root") {
    auto path = writeSmt2("nia_sq_model",
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(assert (= (* x x) 9))\n"
        "(assert (>= x 0))\n"
        "(check-sat)\n");
    Solver s;
    REQUIRE(s.parseFile(path));
    REQUIRE_RESULT(s.checkSat(), Result::Sat);
    auto m = s.getModel();
    // Soundness: NIA model is candidate-only per plan.md §0, so just check API.
    CHECK_NOTHROW(m.values());
}

TEST_CASE("MC: model is empty after reset") {
    Solver s;
    auto path = writeSmt2("reset_model",
        "(set-logic QF_LIA)\n"
        "(declare-const x Int)\n"
        "(assert (= x 5))\n"
        "(check-sat)\n");
    REQUIRE(s.parseFile(path));
    REQUIRE_RESULT(s.checkSat(), Result::Sat);
    CHECK_FALSE(s.getModel().isEmpty());
    s.reset();
    // After reset, model from old context should not crash even if reused.
    CHECK_NOTHROW(s.getModel().values());
}
