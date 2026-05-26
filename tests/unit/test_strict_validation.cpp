// ZOLVER_PP_STRICT_VALIDATION: emit `sat` only on a POSITIVELY-confirmed model.
// A model the independent validator cannot fully evaluate (Indeterminate — e.g.
// an uninterpreted function the validator has no interpretation for) must NOT
// escape as sat; it is downgraded to `unknown`. This only ever turns
// sat -> unknown, so it can never introduce a wrong answer.
#include <doctest/doctest.h>
#include "zolver/Solver.h"
#include <cstdlib>
#include <fstream>
#include <filesystem>
#include <string>

using namespace zolver;

namespace {
struct StrictEnv {
    StrictEnv()  { setenv("ZOLVER_PP_STRICT_VALIDATION", "1", 1); }
    ~StrictEnv() { unsetenv("ZOLVER_PP_STRICT_VALIDATION"); }
};
Result solveStr(const std::string& smt, const std::string& tag) {
    std::string path = (std::filesystem::temp_directory_path() /
                        ("zolver_sv_" + tag + ".smt2")).string();
    { std::ofstream(path) << smt; }
    Solver s;
    REQUIRE(s.parseFile(path));
    return s.checkSat();
}
} // namespace

TEST_CASE("strict-validation: confirmable models stay sat") {
    StrictEnv guard;
    // Pure boolean (values come from the SAT assignment, populated by the gate).
    CHECK(static_cast<int>(solveStr(
        "(declare-const p Bool)(assert (or p (not p)))(check-sat)\n", "bool"))
        == static_cast<int>(Result::Sat));
    // Pure boolean, forced value.
    CHECK(static_cast<int>(solveStr(
        "(declare-const p Bool)(assert p)(check-sat)\n", "p"))
        == static_cast<int>(Result::Sat));
    // Linear integer arithmetic (numeric model is positively evaluable).
    CHECK(static_cast<int>(solveStr(
        "(set-logic QF_LIA)(declare-const x Int)(assert (> x 5))(check-sat)\n", "arith"))
        == static_cast<int>(Result::Sat));
    // Mixed bool + arith.
    CHECK(static_cast<int>(solveStr(
        "(set-logic QF_LIA)(declare-const p Bool)(declare-const x Int)"
        "(assert (and p (> x 5)))(check-sat)\n", "mix"))
        == static_cast<int>(Result::Sat));
}

TEST_CASE("strict-validation: unconfirmable (UF) model is downgraded to unknown") {
    StrictEnv guard;
    // Genuinely sat, but the validator has no interpretation for the
    // uninterpreted function f, so the model is Indeterminate -> unknown.
    Result r = solveStr(
        "(set-logic QF_UF)(declare-sort U 0)(declare-fun f (U) U)"
        "(declare-const a U)(assert (= (f a) (f a)))(check-sat)\n", "uf");
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unknown));
}

TEST_CASE("strict-validation: unsat is unaffected") {
    StrictEnv guard;
    // The gate only ever touches a Sat verdict; unsat passes through.
    CHECK(static_cast<int>(solveStr(
        "(set-logic QF_LIA)(declare-const x Int)"
        "(assert (and (> x 5) (< x 2)))(check-sat)\n", "unsat"))
        == static_cast<int>(Result::Unsat));
}
