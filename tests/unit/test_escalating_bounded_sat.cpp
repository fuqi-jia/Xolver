// Tests for XOLVER_ESCALATING_BOUNDED_SAT — the sound escalating-bounded SAT
// fast-path with a constraint-DERIVED seed bound.
//
// For a free integer variable coupled linearly to bounded vars, its witness
// magnitude is bounded by |v| <= M / C, where M = max magnitude of the bounded
// vars' explicit bounds and C = smallest coefficient the free var is multiplied
// by. The fast-path solves  original ∪ {free-var bounds in [-K,K]}  for K = K0,
// 2*K0, ... (K0 the derived seed). A model of the bounded problem satisfies the
// original (original ⊆ bounded), so SAT is a sound witness; UNSAT of a box is
// never returned (escalate / fall back to a normal solve).
//
// The flag is default-OFF and SOUND regardless of value: these tests confirm
// the ON path reaches the SAME verdict as the OFF path. The fast-path requires
// a re-parseable file source, so the tests drive it via Solver::parseFile.

#include <doctest/doctest.h>
#include <xolver/Solver.h>
#include <xolver/Result.h>
#include <cstdlib>
#include <fstream>
#include <filesystem>

using namespace xolver;

namespace {

std::string writeTempSmt2(const std::string& content, const std::string& tag) {
    std::string path =
        std::filesystem::temp_directory_path() / ("xolver_ebs_" + tag + ".smt2");
    std::ofstream ofs(path);
    ofs << content;
    return path;
}

Result solveFile(const std::string& path) {
    Solver s;
    REQUIRE(s.parseFile(path));
    return s.checkSat();
}

// Free integer var `b` coupled to bounded `w` (w in [0,3]) by 2*b = w. `b` is
// syntactically unbounded but |b| <= M/C = 3/2 -> derived seed K0 = 2. SAT
// (e.g. b=0, w=0).
const char* kSat =
    "(set-logic QF_LIA)\n"
    "(declare-fun b () Int)\n"
    "(declare-fun w () Int)\n"
    "(assert (>= w 0))(assert (<= w 3))\n"
    "(assert (= (* 2 b) w))\n"
    "(check-sat)\n";

// Same coupling plus 2*b = 1, impossible for integer b -> UNSAT. Every bounded
// box is UNSAT, so the fast-path must escalate and fall back, never SAT.
const char* kUnsat =
    "(set-logic QF_LIA)\n"
    "(declare-fun b () Int)\n"
    "(declare-fun w () Int)\n"
    "(assert (>= w 0))(assert (<= w 3))\n"
    "(assert (= (* 2 b) w))\n"
    "(assert (= (* 2 b) 1))\n"
    "(check-sat)\n";

} // namespace

TEST_CASE("XOLVER_ESCALATING_BOUNDED_SAT: SAT verdict preserved ON vs OFF") {
    std::string satPath = writeTempSmt2(kSat, "sat");

    unsetenv("XOLVER_ESCALATING_BOUNDED_SAT");
    Result off = solveFile(satPath);
    CHECK(static_cast<int>(off) == static_cast<int>(Result::Sat));

    // ON: derived seed bounds `b`, the bounded problem is SAT, and its model
    // satisfies the original -> still SAT.
    setenv("XOLVER_ESCALATING_BOUNDED_SAT", "1", 1);
    Result on = solveFile(satPath);
    CHECK(static_cast<int>(on) == static_cast<int>(Result::Sat));
    unsetenv("XOLVER_ESCALATING_BOUNDED_SAT");
}

TEST_CASE("XOLVER_ESCALATING_BOUNDED_SAT: never emits SAT for an UNSAT problem") {
    std::string unsatPath = writeTempSmt2(kUnsat, "unsat");

    unsetenv("XOLVER_ESCALATING_BOUNDED_SAT");
    Result off = solveFile(unsatPath);
    CHECK(static_cast<int>(off) == static_cast<int>(Result::Unsat));

    // ON (multiple rounds): every bounded box is UNSAT; the fast-path must NEVER
    // conclude SAT from a box -> it escalates and falls back to a normal solve.
    setenv("XOLVER_ESCALATING_BOUNDED_SAT", "3", 1);
    Result on = solveFile(unsatPath);
    CHECK(static_cast<int>(on) != static_cast<int>(Result::Sat));
    unsetenv("XOLVER_ESCALATING_BOUNDED_SAT");
}
