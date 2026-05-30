#include <doctest/doctest.h>
#include "xolver/Solver.h"
#include <cstdlib>
#include <filesystem>
#include <fstream>

using namespace xolver;

#define CHECK_RESULT(actual, expected) \
    CHECK(static_cast<int>(actual) == static_cast<int>(expected))

namespace {

struct ZoharEnvGuard {
    ZoharEnvGuard()  { setenv("XOLVER_NIA_ZOHAR_PLUGIN", "1", 1); }
    ~ZoharEnvGuard() { unsetenv("XOLVER_NIA_ZOHAR_PLUGIN"); }
};

std::string write(const std::string& tag, const std::string& body) {
    auto p = std::filesystem::temp_directory_path() /
             ("xolver_zohar_" + tag + ".smt2");
    std::ofstream(p) << body;
    return p.string();
}

Result solve(const std::string& path) {
    Solver s;
    REQUIRE(s.parseFile(path));
    return s.checkSat();
}

} // namespace

// ----------------------- AXIOM SOUNDNESS (z3-validated) ----------------------
//
// The Phase 1 axioms emitted by ZoharBwiAxiomEmitter are:
//   1. (= (pow2 0) 1)
//   2. for every (pow2 t) in the formula: (=> (>= t 0) (>= (pow2 t) 1))
//
// Each axiom is MATHEMATICALLY VALID under the standard interpretation
// pow2(n) = 2^n on n >= 0 — i.e. z3 considers the negation UNSAT.  These
// tests pin that the plugin's axioms align with z3's view of pow2:
//
//   "axiom AND not axiom" must be UNSAT with the plugin on.
//
// (Phrased as a solver test: assert the NEGATION of the axiom and check that
// the plugin's axiom contradicts it -> UNSAT. Without the plugin, the same
// formula is SAT because `pow2` is uninterpreted.)

TEST_CASE("Zohar Phase 1: ground axiom (pow2 0) = 1 is z3-valid; plugin asserts it") {
    auto path = write("ground_neg",
        "(set-logic QF_UFNIA)\n"
        "(declare-fun pow2 (Int) Int)\n"
        "(assert (not (= (pow2 0) 1)))\n"
        "(check-sat)\n");
    {
        ZoharEnvGuard g;
        CHECK_RESULT(solve(path), Result::Unsat); // plugin asserts (pow2 0) = 1
    }
    CHECK_RESULT(solve(path), Result::Sat);       // without plugin, pow2 free
}

TEST_CASE("Zohar Phase 1: per-term axiom (>= 0 t) -> (>= (pow2 t) 1) is z3-valid") {
    auto path = write("perterm_neg",
        "(set-logic QF_UFNIA)\n"
        "(declare-fun pow2 (Int) Int)\n"
        "(declare-fun n () Int)\n"
        "(assert (>= n 0))\n"
        "(assert (< (pow2 n) 1))\n"
        "(check-sat)\n");
    {
        ZoharEnvGuard g;
        CHECK_RESULT(solve(path), Result::Unsat); // plugin asserts pow2(n) >= 1
    }
    CHECK_RESULT(solve(path), Result::Sat);       // without plugin, pow2 free
}

TEST_CASE("Zohar Phase 1: per-term axiom does NOT restrict negative t (sound)") {
    // pow2(-1) is left undefined under the standard interpretation. The axiom
    // is (=> (>= t 0) ...) — it must not constrain pow2(-1). The test asserts
    // a model exists where pow2(-1) = 0, which the standard interpretation
    // allows. With the plugin: still sat. (No false-UNSAT.)
    auto path = write("neg_arg",
        "(set-logic QF_UFNIA)\n"
        "(declare-fun pow2 (Int) Int)\n"
        "(assert (= (pow2 (- 1)) 0))\n"
        "(check-sat)\n");
    ZoharEnvGuard g;
    CHECK_RESULT(solve(path), Result::Sat);
}

// ------------------------ PRESENCE + EMPTY NO-OP -----------------------------

TEST_CASE("Zohar Phase 1: empty no-op when no pow2 UF appears") {
    auto path = write("nopow2",
        "(set-logic QF_NIA)\n"
        "(declare-fun x () Int)\n"
        "(assert (= (* x x) 16))\n"
        "(check-sat)\n");
    ZoharEnvGuard g;
    CHECK_RESULT(solve(path), Result::Sat);
}

TEST_CASE("Zohar Phase 1: SAT case preserved (no false-UNSAT)") {
    // A pow2 case satisfiable under the standard interpretation.
    // The plugin's axioms must NOT turn it UNSAT (false-UNSAT = invariant 7
    // violation). Unknown is acceptable here — EUF+NIA model construction for
    // uninterpreted functions is the broader combination capability
    // (EQNA Track 3 XOLVER_EUF_UF_MODEL), out of scope for the plugin itself.
    auto path = write("sat_preserved",
        "(set-logic QF_UFNIA)\n"
        "(declare-fun pow2 (Int) Int)\n"
        "(declare-fun k () Int)\n"
        "(assert (>= k 0))\n"
        "(assert (= (pow2 k) (pow2 k)))\n"
        "(check-sat)\n");
    ZoharEnvGuard g;
    Result r = solve(path);
    CHECK((r == Result::Sat || r == Result::Unknown));
}
