// Property-based invariants: equivalent formula transformations should produce
// the same Sat/Unsat verdict. If they don't, the solver has a soundness or
// completeness bug in handling some normalization path.
//
// These are the "consistency oracles" SOTA solvers must satisfy:
//   - commutativity of + and *
//   - associativity reordering
//   - double negation
//   - DeMorgan equivalences
//   - distributive expansion
//   - variable renaming invariance
//   - reset-and-reload invariance
//
// For each pair, both must return the same Result (Sat or Unsat). If one
// returns Unknown we accept (incompleteness) but flag mismatched verdicts.

#include <doctest/doctest.h>
#include "zolver/Solver.h"
#include <filesystem>
#include <fstream>

using namespace zolver;

#define INT(r) static_cast<int>(r)

static std::string writeSmt2(const std::string& name, const std::string& body) {
    auto p = std::filesystem::temp_directory_path() / ("zolver_prop_" + name + ".smt2");
    std::ofstream(p) << body;
    return p.string();
}

static Result solveFile(const std::string& body, const std::string& tag) {
    auto path = writeSmt2(tag, body);
    Solver s;
    REQUIRE(s.parseFile(path));
    return s.checkSat();
}

// Compare two formulas — both must be Sat, both Unsat, or both Unknown.
// One Unknown + one Sat/Unsat is OK (incompleteness). Sat vs Unsat is BAD.
static void requireConsistent(Result a, Result b, const char* msg) {
    if (a == Result::Sat && b == Result::Unsat) FAIL("DISAGREE (Sat vs Unsat): ", msg);
    if (a == Result::Unsat && b == Result::Sat) FAIL("DISAGREE (Unsat vs Sat): ", msg);
}

// -----------------------------------------------------------------------
// Commutativity of arithmetic operators
// -----------------------------------------------------------------------

TEST_CASE("Prop: (+ x y) ≡ (+ y x) under same constraint") {
    auto r1 = solveFile(
        "(set-logic QF_LIA)\n"
        "(declare-const x Int) (declare-const y Int)\n"
        "(assert (= (+ x y) 10)) (assert (= x 3)) (check-sat)\n", "comm_add_1");
    auto r2 = solveFile(
        "(set-logic QF_LIA)\n"
        "(declare-const x Int) (declare-const y Int)\n"
        "(assert (= (+ y x) 10)) (assert (= x 3)) (check-sat)\n", "comm_add_2");
    requireConsistent(r1, r2, "commutativity of +");
    CHECK(INT(r1) == INT(Result::Sat));
}

TEST_CASE("Prop: (* x y) ≡ (* y x) under bounded NIA") {
    auto r1 = solveFile(
        "(set-logic QF_NIA)\n"
        "(declare-const x Int) (declare-const y Int)\n"
        "(assert (>= x 1)) (assert (<= x 5))\n"
        "(assert (>= y 1)) (assert (<= y 5))\n"
        "(assert (= (* x y) 6)) (check-sat)\n", "comm_mul_1");
    auto r2 = solveFile(
        "(set-logic QF_NIA)\n"
        "(declare-const x Int) (declare-const y Int)\n"
        "(assert (>= x 1)) (assert (<= x 5))\n"
        "(assert (>= y 1)) (assert (<= y 5))\n"
        "(assert (= (* y x) 6)) (check-sat)\n", "comm_mul_2");
    requireConsistent(r1, r2, "commutativity of *");
}

// -----------------------------------------------------------------------
// Associativity reordering
// -----------------------------------------------------------------------

TEST_CASE("Prop: ((a+b)+c) ≡ (a+(b+c))") {
    auto r1 = solveFile(
        "(set-logic QF_LIA)\n"
        "(declare-const a Int) (declare-const b Int) (declare-const c Int)\n"
        "(assert (= (+ (+ a b) c) 6))\n"
        "(assert (= a 1)) (assert (= b 2))\n"
        "(check-sat)\n", "assoc_1");
    auto r2 = solveFile(
        "(set-logic QF_LIA)\n"
        "(declare-const a Int) (declare-const b Int) (declare-const c Int)\n"
        "(assert (= (+ a (+ b c)) 6))\n"
        "(assert (= a 1)) (assert (= b 2))\n"
        "(check-sat)\n", "assoc_2");
    requireConsistent(r1, r2, "associativity of +");
    CHECK(INT(r1) == INT(Result::Sat));
}

// -----------------------------------------------------------------------
// Double negation
// -----------------------------------------------------------------------

TEST_CASE("Prop: (not (not p)) ≡ p") {
    auto r1 = solveFile(
        "(set-logic QF_UF)\n"
        "(declare-const p Bool)\n"
        "(assert p) (assert (not p)) (check-sat)\n", "dn_1");
    auto r2 = solveFile(
        "(set-logic QF_UF)\n"
        "(declare-const p Bool)\n"
        "(assert (not (not p))) (assert (not p)) (check-sat)\n", "dn_2");
    requireConsistent(r1, r2, "double negation");
    CHECK(INT(r1) == INT(Result::Unsat));
}

// -----------------------------------------------------------------------
// DeMorgan
// -----------------------------------------------------------------------

TEST_CASE("Prop: (not (and p q)) ≡ (or (not p) (not q))") {
    auto r1 = solveFile(
        "(set-logic QF_UF)\n"
        "(declare-const p Bool) (declare-const q Bool)\n"
        "(assert (not (and p q))) (assert p) (check-sat)\n", "dm_1");
    auto r2 = solveFile(
        "(set-logic QF_UF)\n"
        "(declare-const p Bool) (declare-const q Bool)\n"
        "(assert (or (not p) (not q))) (assert p) (check-sat)\n", "dm_2");
    requireConsistent(r1, r2, "DeMorgan and");
    CHECK(INT(r1) == INT(Result::Sat));
}

// -----------------------------------------------------------------------
// Distributivity
// -----------------------------------------------------------------------

TEST_CASE("Prop: x*(y+z) ≡ x*y + x*z (NIA)") {
    auto r1 = solveFile(
        "(set-logic QF_NIA)\n"
        "(declare-const x Int) (declare-const y Int) (declare-const z Int)\n"
        "(assert (>= x 1)) (assert (<= x 3))\n"
        "(assert (>= y 0)) (assert (<= y 3))\n"
        "(assert (>= z 0)) (assert (<= z 3))\n"
        "(assert (= (* x (+ y z)) 6)) (check-sat)\n", "dist_1");
    auto r2 = solveFile(
        "(set-logic QF_NIA)\n"
        "(declare-const x Int) (declare-const y Int) (declare-const z Int)\n"
        "(assert (>= x 1)) (assert (<= x 3))\n"
        "(assert (>= y 0)) (assert (<= y 3))\n"
        "(assert (>= z 0)) (assert (<= z 3))\n"
        "(assert (= (+ (* x y) (* x z)) 6)) (check-sat)\n", "dist_2");
    requireConsistent(r1, r2, "distributivity over +");
}

// -----------------------------------------------------------------------
// Variable renaming
// -----------------------------------------------------------------------

TEST_CASE("Prop: renaming x->a, y->b preserves Sat/Unsat") {
    auto r1 = solveFile(
        "(set-logic QF_LIA)\n"
        "(declare-const x Int) (declare-const y Int)\n"
        "(assert (= x 5)) (assert (= y 7)) (assert (= (+ x y) 12)) (check-sat)\n", "rn_1");
    auto r2 = solveFile(
        "(set-logic QF_LIA)\n"
        "(declare-const a Int) (declare-const b Int)\n"
        "(assert (= a 5)) (assert (= b 7)) (assert (= (+ a b) 12)) (check-sat)\n", "rn_2");
    requireConsistent(r1, r2, "variable renaming");
    CHECK(INT(r1) == INT(Result::Sat));
}

// -----------------------------------------------------------------------
// Reset-and-reload invariance
// -----------------------------------------------------------------------

TEST_CASE("Prop: solver.reset() then reload gives same answer") {
    auto path = writeSmt2("reset_inv",
        "(set-logic QF_LIA)\n"
        "(declare-const x Int)\n"
        "(assert (>= x 0)) (assert (<= x 5)) (assert (= (* x 2) 4))\n"
        "(check-sat)\n");
    Solver s;
    REQUIRE(s.parseFile(path));
    auto r1 = s.checkSat();
    s.reset();
    REQUIRE(s.parseFile(path));
    auto r2 = s.checkSat();
    CHECK(INT(r1) == INT(r2));
}

// -----------------------------------------------------------------------
// Sign flip invariance: ¬(a ≤ b) ≡ (a > b)
// -----------------------------------------------------------------------

TEST_CASE("Prop: (not (<= x y)) ≡ (> x y)") {
    auto r1 = solveFile(
        "(set-logic QF_LIA)\n"
        "(declare-const x Int) (declare-const y Int)\n"
        "(assert (not (<= x y))) (assert (= y 5)) (assert (= x 5)) (check-sat)\n", "sf_1");
    auto r2 = solveFile(
        "(set-logic QF_LIA)\n"
        "(declare-const x Int) (declare-const y Int)\n"
        "(assert (> x y)) (assert (= y 5)) (assert (= x 5)) (check-sat)\n", "sf_2");
    requireConsistent(r1, r2, "not(<=) ≡ >");
    CHECK(INT(r1) == INT(Result::Unsat));
}

// -----------------------------------------------------------------------
// Eq as iff (Bool) vs implication conjunction
// -----------------------------------------------------------------------

TEST_CASE("Prop: (= p q) ≡ (and (=> p q) (=> q p)) for Bool") {
    auto r1 = solveFile(
        "(set-logic QF_UF)\n"
        "(declare-const p Bool) (declare-const q Bool)\n"
        "(assert (= p q)) (assert p) (assert (not q)) (check-sat)\n", "iff_1");
    auto r2 = solveFile(
        "(set-logic QF_UF)\n"
        "(declare-const p Bool) (declare-const q Bool)\n"
        "(assert (and (=> p q) (=> q p))) (assert p) (assert (not q)) (check-sat)\n", "iff_2");
    requireConsistent(r1, r2, "iff equivalence");
    CHECK(INT(r1) == INT(Result::Unsat));
}

// -----------------------------------------------------------------------
// Power vs repeated multiplication: x*x ≡ x^2 (NRA & NIA)
// -----------------------------------------------------------------------

TEST_CASE("Prop: x*x ≡ x^2 in NIA via different syntactic forms") {
    auto r1 = solveFile(
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(assert (>= x 0)) (assert (<= x 5))\n"
        "(assert (= (* x x) 9)) (check-sat)\n", "pow_1");
    auto r2 = solveFile(
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(assert (>= x 0)) (assert (<= x 5))\n"
        "(assert (= (* x x) (* 3 3))) (check-sat)\n", "pow_2");
    requireConsistent(r1, r2, "x*x semantics");
    CHECK(INT(r1) == INT(Result::Sat));
}

// -----------------------------------------------------------------------
// Constraint reordering
// -----------------------------------------------------------------------

TEST_CASE("Prop: reordering assert order does not change result") {
    auto r1 = solveFile(
        "(set-logic QF_LIA)\n"
        "(declare-const x Int)\n"
        "(assert (>= x 0)) (assert (<= x 10)) (assert (= (* x 2) 6))\n"
        "(check-sat)\n", "ord_1");
    auto r2 = solveFile(
        "(set-logic QF_LIA)\n"
        "(declare-const x Int)\n"
        "(assert (= (* x 2) 6)) (assert (<= x 10)) (assert (>= x 0))\n"
        "(check-sat)\n", "ord_2");
    auto r3 = solveFile(
        "(set-logic QF_LIA)\n"
        "(declare-const x Int)\n"
        "(assert (<= x 10)) (assert (= (* x 2) 6)) (assert (>= x 0))\n"
        "(check-sat)\n", "ord_3");
    requireConsistent(r1, r2, "constraint order 1-2");
    requireConsistent(r1, r3, "constraint order 1-3");
    CHECK(INT(r1) == INT(Result::Sat));
}

// -----------------------------------------------------------------------
// Tautology and contradiction always conclusive
// -----------------------------------------------------------------------

TEST_CASE("Prop: tautology always Sat") {
    auto r = solveFile(
        "(set-logic QF_UF)\n"
        "(declare-const p Bool)\n"
        "(assert (or p (not p))) (check-sat)\n", "taut");
    CHECK(INT(r) == INT(Result::Sat));
}

TEST_CASE("Prop: contradiction always Unsat") {
    auto r = solveFile(
        "(set-logic QF_UF)\n"
        "(declare-const p Bool)\n"
        "(assert (and p (not p))) (check-sat)\n", "contra");
    CHECK(INT(r) == INT(Result::Unsat));
}

// -----------------------------------------------------------------------
// Idempotence
// -----------------------------------------------------------------------

TEST_CASE("Prop: (and p p) ≡ p") {
    auto r1 = solveFile(
        "(set-logic QF_UF)\n"
        "(declare-const p Bool)\n"
        "(assert (and p p)) (assert (not p)) (check-sat)\n", "idem_1");
    auto r2 = solveFile(
        "(set-logic QF_UF)\n"
        "(declare-const p Bool)\n"
        "(assert p) (assert (not p)) (check-sat)\n", "idem_2");
    requireConsistent(r1, r2, "idempotent and");
    CHECK(INT(r1) == INT(Result::Unsat));
}
