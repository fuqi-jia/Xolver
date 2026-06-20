// Array + arithmetic (+ UF) combination logics: QF_ALIA / QF_ALRA /
// QF_AUFLIA / QF_AUFLRA.
//
// These exercise Nelson-Oppen combination where array index/element terms are
// arithmetic and shared with the LIA/LRA solver (and, for AUF*, with UF). The
// key soundness path is Row2 over ARITH indices: the (i=j) antecedent must be
// a shared-equality atom observed by BOTH arith and EUF, so an arith fact like
// (= i (+ j 0)) drives the Row2 case split. Verdicts cross-checked vs z3+cvc5.

#include "xolver/Solver.h"
#include <doctest/doctest.h>
#include <fstream>
#include <filesystem>
#include <cstdlib>

using namespace xolver;

static std::string writeComboSmt2(const std::string& content) {
    static int counter = 0;
    std::string path = std::filesystem::temp_directory_path() /
        ("xolver_array_combo_test_" + std::to_string(counter++) + ".smt2");
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

// ---- #69 store-vs-base extensionality (gated default-OFF) -----------------

// store(c, j, k+1) != c with a COMPOUND value is sat (c[j] can differ from
// k+1), and z3/cvc5 both agree. By default Xolver floors it to unknown: the
// disequality select(c,j) != k+1 is never propagated to arith, so the
// candidate model makes the store a no-op and the validator cannot confirm.
// The sound preprocessing biconditional (store=c) <-> (select(c,j)=v), gated
// behind XOLVER_AX_STORE_VS_BASE, recovers sat. This exercises both the
// default floor and the flag-ON recovery so the gated lever cannot bit-rot.
TEST_CASE("QF_ALIA #69 store-vs-base compound value: floor + gated recovery") {
    const char* smt =
        "(set-logic QF_ALIA)\n"
        "(declare-fun c () (Array Int Int))\n"
        "(declare-fun j () Int)\n"
        "(declare-fun k () Int)\n"
        "(assert (not (= (store c j (+ k 1)) c)))\n"
        "(check-sat)\n";

    // Default (flag OFF): sound completeness floor -> unknown (never a wrong
    // verdict; z3/cvc5 say sat).
    unsetenv("XOLVER_AX_STORE_VS_BASE");
    Result off = solveStr(smt);
    CHECK(static_cast<int>(off) == static_cast<int>(Result::Unknown));

    // Flag ON: the biconditional axiom recovers the genuine sat (the model is
    // independently re-validated by the ModelValidator before sat is emitted).
    setenv("XOLVER_AX_STORE_VS_BASE", "1", 1);
    Result on = solveStr(smt);
    unsetenv("XOLVER_AX_STORE_VS_BASE");
    CHECK(static_cast<int>(on) == static_cast<int>(Result::Sat));
}

// ---- #85 model-driven array refinement (XOLVER_AX_REFINE) ----------------
// QF_AX storeinv multi-store residual: (= a_33 a_35) collapses two stores with
// DIFFERENT bases into one e-graph class. The lazy Row2 lemma set exhausts
// (row2Done_ saturates) while the candidate model still VIOLATES a Row2 instance
// (select(s,k), select(a,k) left unmerged at k != write-index) — so the model is
// array-inconsistent and floors to Unknown (sound). The refinement re-scans at a
// Full-effort consistent model with a fresh dedup + onlyViolated, re-asserts the
// exact missed instance, and drives the SAT solver to a consistent model (the
// principled lazy-array completeness mechanism). z3/cvc5 both say sat; the model
// is independently re-validated by the ModelValidator before sat is emitted.
TEST_CASE("QF_AX #85 storeinv multi-store: floor + gated refinement recovery") {
    std::string smt =
        "(set-logic QF_AX)\n"
        "(declare-sort Index 0)\n(declare-sort Element 0)\n"
        "(declare-fun a_1 () (Array Index Element))(declare-fun a_11 () (Array Index Element))\n"
        "(declare-fun a_13 () (Array Index Element))(declare-fun a_15 () (Array Index Element))\n"
        "(declare-fun a_17 () (Array Index Element))(declare-fun a_19 () (Array Index Element))\n"
        "(declare-fun a_21 () (Array Index Element))(declare-fun a_23 () (Array Index Element))\n"
        "(declare-fun a_25 () (Array Index Element))(declare-fun a_27 () (Array Index Element))\n"
        "(declare-fun a_29 () (Array Index Element))(declare-fun a_3 () (Array Index Element))\n"
        "(declare-fun a_31 () (Array Index Element))(declare-fun a_33 () (Array Index Element))\n"
        "(declare-fun a_35 () (Array Index Element))(declare-fun a_5 () (Array Index Element))\n"
        "(declare-fun a_7 () (Array Index Element))(declare-fun a_9 () (Array Index Element))\n"
        "(declare-fun e_0 () Element)(declare-fun e_10 () Element)(declare-fun e_12 () Element)\n"
        "(declare-fun e_14 () Element)(declare-fun e_16 () Element)(declare-fun e_18 () Element)\n"
        "(declare-fun e_2 () Element)(declare-fun e_20 () Element)(declare-fun e_22 () Element)\n"
        "(declare-fun e_24 () Element)(declare-fun e_26 () Element)(declare-fun e_28 () Element)\n"
        "(declare-fun e_30 () Element)(declare-fun e_32 () Element)(declare-fun e_34 () Element)\n"
        "(declare-fun e_4 () Element)(declare-fun e_6 () Element)(declare-fun e_8 () Element)\n"
        "(declare-fun a1 () (Array Index Element))(declare-fun a2 () (Array Index Element))\n"
        "(declare-fun i1 () Index)(declare-fun i2 () Index)(declare-fun i3 () Index)\n"
        "(declare-fun i4 () Index)(declare-fun i5 () Index)(declare-fun i6 () Index)\n"
        "(declare-fun i7 () Index)(declare-fun i8 () Index)(declare-fun i9 () Index)\n"
        "(assert (= a_1 (store a1 i1 e_0)))(assert (= a_11 (store a_7 i3 e_10)))\n"
        "(assert (= a_13 (store a_9 i4 e_12)))(assert (= a_15 (store a_11 i4 e_14)))\n"
        "(assert (= a_17 (store a_13 i5 e_16)))(assert (= a_19 (store a_15 i5 e_18)))\n"
        "(assert (= a_21 (store a_17 i6 e_20)))(assert (= a_23 (store a_19 i6 e_22)))\n"
        "(assert (= a_25 (store a_21 i7 e_24)))(assert (= a_27 (store a_23 i7 e_26)))\n"
        "(assert (= a_29 (store a_25 i8 e_28)))(assert (= a_3 (store a2 i1 e_2)))\n"
        "(assert (= a_31 (store a_27 i8 e_30)))(assert (= a_33 (store a_29 i1 e_32)))\n"
        "(assert (= a_35 (store a_31 i9 e_34)))(assert (= a_5 (store a_1 i2 e_4)))\n"
        "(assert (= a_7 (store a_3 i2 e_6)))(assert (= a_9 (store a_5 i3 e_8)))\n"
        "(assert (= e_0 (select a2 i1)))(assert (= e_10 (select a_5 i3)))\n"
        "(assert (= e_12 (select a_11 i4)))(assert (= e_14 (select a_9 i4)))\n"
        "(assert (= e_16 (select a_15 i5)))(assert (= e_18 (select a_13 i5)))\n"
        "(assert (= e_2 (select a1 i1)))(assert (= e_20 (select a_19 i6)))\n"
        "(assert (= e_22 (select a_17 i6)))(assert (= e_24 (select a_23 i7)))\n"
        "(assert (= e_26 (select a_21 i7)))(assert (= e_28 (select a_27 i8)))\n"
        "(assert (= e_30 (select a_25 i8)))(assert (= e_32 (select a_31 i9)))\n"
        "(assert (= e_34 (select a_29 i9)))(assert (= e_4 (select a_3 i2)))\n"
        "(assert (= e_6 (select a_1 i2)))(assert (= e_8 (select a_7 i3)))\n"
        "(assert (= a_33 a_35))(assert (not (= a1 a2)))\n"
        "(check-sat)\n";

    // Replicate the competition-baked config: XOLVER_AX_ROW2_CONST=1 (a baked
    // default the CLI sets) is what makes the eager Row2-const path leave this
    // multi-store class array-incomplete, so the lazy lemma set exhausts on an
    // inconsistent model. The Solver API does NOT apply the baked defaults, so set
    // it explicitly here to reproduce the floor the shipped binary hits.
    setenv("XOLVER_AX_ROW2_CONST", "1", 1);

    // Refinement OFF: sound completeness floor -> unknown (never a wrong verdict).
    unsetenv("XOLVER_AX_REFINE");
    Result off = solveStr(smt);
    CHECK(static_cast<int>(off) == static_cast<int>(Result::Unknown));

    // Refinement ON: re-asserts the violated Row2 instance and converges to the
    // genuine sat (ModelValidator-confirmed before sat is emitted).
    setenv("XOLVER_AX_REFINE", "1", 1);
    Result on = solveStr(smt);
    unsetenv("XOLVER_AX_REFINE");
    unsetenv("XOLVER_AX_ROW2_CONST");
    CHECK(static_cast<int>(on) == static_cast<int>(Result::Sat));
}

}  // TEST_SUITE
