#include <doctest/doctest.h>
#include "zolver/Solver.h"
#include <filesystem>
#include <fstream>
#include <cstdlib>

using namespace zolver;

// Phase-1 combination-arrangement: the certificate floor (ZOLVER_COMB_SAT_FLOOR)
// decides completeness from shared-arg MODEL-COINCIDENCE (so it never under-floors
// a genuine obligation) MINUS asserted disequality (so an asserted (distinct a b)
// is recognised as a recoverable model artifact, not an obligation).
//
//  * uflra_007 shape: (distinct a b) asserted; the buggy extracted model coincides
//    a=b, but the interface disequality marks them separable, so the UF apps
//    f(a)/f(b) carry no congruence obligation -> SAT must be preserved (the bare
//    extracted-model detector OVER-FLOORED this to Unknown).
//  * Wisa relational shape: two registered shared scalars forced equal by linear
//    arithmetic (z=fmt1+1, z=k+1 => fmt1=k), no disequality; f(fmt1)/f(k)
//    congruence is a genuine obligation -> FLOOR downgrades to Unknown (sound);
//    ARRANGE recovers UNSAT.
//  * Wisa compound shape: a UF argument is a compound term (sf(fmt1+1)) purified
//    to an internal bridge var the detector is otherwise blind to. Registering it
//    as an arrangeable shared term makes FLOOR see the obligation (Unknown) and
//    ARRANGE recover the correct UNSAT.
//
// All flags are DEFAULT OFF (promotion gated on panda A/B); the tests set them.

namespace {
std::string writeTmp(const std::string& name, const std::string& body) {
    auto p = std::filesystem::temp_directory_path() / ("zolver_pa_" + name + ".smt2");
    std::ofstream(p) << body;
    return p.string();
}

Result solve(const std::string& path, bool floor, bool arrange) {
    if (floor)   setenv("ZOLVER_COMB_SAT_FLOOR", "1", 1);
    else         unsetenv("ZOLVER_COMB_SAT_FLOOR");
    if (arrange) setenv("ZOLVER_COMB_UFARG_ARRANGE", "1", 1);
    else         unsetenv("ZOLVER_COMB_UFARG_ARRANGE");
    Solver s;
    REQUIRE(s.parseFile(path));
    Result r = s.checkSat();
    unsetenv("ZOLVER_COMB_SAT_FLOOR");
    unsetenv("ZOLVER_COMB_UFARG_ARRANGE");
    return r;
}

int R(Result r) { return static_cast<int>(r); }

// (distinct a b) coincidentally equated by a buggy extracted model. a != b is NOT
// entailed-equal, so no congruence obligation -> SAT.
const char* kCoincidental =
    "(set-logic QF_UFLRA)\n"
    "(declare-fun f (Real) Real)\n"
    "(declare-const a Real) (declare-const b Real)\n"
    "(assert (distinct a b))\n"
    "(assert (distinct (f a) (f b)))\n"
    "(check-sat)\n";

// Registered shared scalars fmt1,k forced provably equal by linear arithmetic;
// distinct f-images contradict the entailed congruence. UNSAT.
const char* kRelational =
    "(set-logic QF_UFLIA)\n"
    "(declare-fun sf (Int) Int)\n"
    "(declare-const fmt1 Int) (declare-const k Int) (declare-const z Int)\n"
    "(assert (= z (+ fmt1 1)))\n"
    "(assert (= z (+ k 1)))\n"
    "(assert (distinct (sf fmt1) (sf k)))\n"
    "(check-sat)\n";

// A compound UF argument (sf (+ fmt1 1)) purified to an internal bridge var,
// provably equal to k. UNSAT, but the bridge var must be arrangeable to see it.
const char* kCompound =
    "(set-logic QF_UFLIA)\n"
    "(declare-fun sf (Int) Int)\n"
    "(declare-const fmt1 Int) (declare-const k Int)\n"
    "(assert (= k (+ fmt1 1)))\n"
    "(assert (distinct (sf (+ fmt1 1)) (sf k)))\n"
    "(check-sat)\n";
} // namespace

TEST_CASE("PA: coincidental (distinct a b) is not over-floored — stays SAT") {
    auto path = writeTmp("coincidental", kCoincidental);
    CHECK(R(solve(path, /*floor=*/true, /*arrange=*/false)) == R(Result::Sat));
}

TEST_CASE("PA: relational shared-scalar congruence floors to Unknown") {
    auto path = writeTmp("relational", kRelational);
    CHECK(R(solve(path, /*floor=*/true, /*arrange=*/false)) == R(Result::Unknown));
}

TEST_CASE("PA: relational shared-scalar congruence recovers to UNSAT") {
    auto path = writeTmp("relational", kRelational);
    CHECK(R(solve(path, /*floor=*/true, /*arrange=*/true)) == R(Result::Unsat));
}

TEST_CASE("PA: compound bridge-arg congruence floors to Unknown") {
    auto path = writeTmp("compound", kCompound);
    CHECK(R(solve(path, /*floor=*/true, /*arrange=*/false)) == R(Result::Unknown));
}

TEST_CASE("PA: compound bridge-arg congruence recovers to UNSAT") {
    auto path = writeTmp("compound", kCompound);
    CHECK(R(solve(path, /*floor=*/true, /*arrange=*/true)) == R(Result::Unsat));
}
