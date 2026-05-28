#include <doctest/doctest.h>
#include "xolver/Solver.h"
#include <filesystem>
#include <fstream>
#include <cstdlib>

using namespace xolver;

// Model-based theory combination (XOLVER_COMB_MODEL_BASED) closes the
// Nelson-Oppen arrangement over shared scalars before reporting Sat, fixing the
// existing QF_UFLIA combination false-SAT class (a genuinely UNSAT UF pigeonhole
// over a bounded integer domain was reported sat because the arrangement that
// exposes the congruence conflict was never decided).
//
// The fix is DEFAULT OFF (promotion gated on panda A/B), so these tests set the
// env flag explicitly. With the flag off the default solver still exhibits the
// false-SAT — that is the known pre-existing bug this flag addresses.

namespace {
std::string writeTmp(const std::string& name, const std::string& body) {
    auto p = std::filesystem::temp_directory_path() / ("xolver_mba_" + name + ".smt2");
    std::ofstream(p) << body;
    return p.string();
}

Result solveWithFlag(const std::string& path, bool flag) {
    if (flag) setenv("XOLVER_COMB_MODEL_BASED", "1", 1);
    else      unsetenv("XOLVER_COMB_MODEL_BASED");
    Solver s;
    REQUIRE(s.parseFile(path));
    Result r = s.checkSat();
    unsetenv("XOLVER_COMB_MODEL_BASED");
    return r;
}

// UF pigeonhole: 3 integers in {0,1}, pairwise-distinct under f. Two must share
// a value (pigeonhole), forcing their f-images equal -> contradicts distinct.
// UNSAT, but requires the shared a=b / b=c / a=c arrangement to be closed.
const char* kPigeonhole =
    "(set-logic QF_UFLIA)\n"
    "(declare-fun f (Int) Int)\n"
    "(declare-fun a () Int) (declare-fun b () Int) (declare-fun c () Int)\n"
    "(assert (>= a 0)) (assert (<= a 1))\n"
    "(assert (>= b 0)) (assert (<= b 1))\n"
    "(assert (>= c 0)) (assert (<= c 1))\n"
    "(assert (distinct (f a) (f b)))\n"
    "(assert (distinct (f b) (f c)))\n"
    "(assert (distinct (f a) (f c)))\n"
    "(check-sat)\n";

// Two integers in {0,1} with distinct f-images: SAT (a=0, b=1). Must NOT become
// a false UNSAT under the arrangement closure.
const char* kSat =
    "(set-logic QF_UFLIA)\n"
    "(declare-fun f (Int) Int)\n"
    "(declare-fun a () Int) (declare-fun b () Int)\n"
    "(assert (>= a 0)) (assert (<= a 1))\n"
    "(assert (>= b 0)) (assert (<= b 1))\n"
    "(assert (distinct (f a) (f b)))\n"
    "(check-sat)\n";
} // namespace

TEST_CASE("MBA: UFLIA pigeonhole is UNSAT once the arrangement is closed") {
    auto path = writeTmp("pigeonhole", kPigeonhole);
    // Flag ON: arrangement closure must surface the congruence conflict.
    CHECK(static_cast<int>(solveWithFlag(path, true)) == static_cast<int>(Result::Unsat));
}

TEST_CASE("MBA: arrangement closure introduces no false UNSAT") {
    auto path = writeTmp("sat", kSat);
    CHECK(static_cast<int>(solveWithFlag(path, true)) != static_cast<int>(Result::Unsat));
}
