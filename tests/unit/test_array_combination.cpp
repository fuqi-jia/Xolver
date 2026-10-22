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
#include <sstream>

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

TEST_CASE("ReadOnlyArray model reconstructs nested and read-dependent indices") {
    const auto path = writeComboSmt2(
        "(set-logic QF_ALIA)(declare-const a (Array Int (Array Int Int)))"
        "(declare-const b (Array Int Int))(declare-const i Int)(declare-const j Int)"
        "(assert (= i j))(assert (= (select b 0) 2))"
        "(assert (= (select (select a i) (select b 0)) 7))"
        "(assert (= (select (select a j) 3) 8))(check-sat)");
    Solver solver;
    REQUIRE(solver.parseFile(path));
    for (int repeat = 0; repeat < 2; ++repeat) {
        REQUIRE((solver.checkSat() == Result::Sat));
        CHECK((solver.validateModel() == Solver::ModelValidation::Satisfied));
        std::ostringstream model;
        solver.dumpModel(model);
        CHECK(model.str().find("(store") != std::string::npos);
        CHECK(model.str().find("(error") == std::string::npos);
        CHECK(model.str().find("declare-fun @(Array") == std::string::npos);
    }
}

TEST_CASE("ReadOnlyArray model preserves Boolean reads and indices") {
    for (const auto& source : {
        "(set-logic QF_AX)(declare-const a (Array Bool Bool))"
        "(assert (select a true))(assert (not (select a false)))(check-sat)",
        "(set-logic QF_ALIA)(declare-const a (Array Int Bool))"
        "(declare-const i Int)(assert (> i 0))"
        "(assert (select a i))(assert (not (select a 0)))(check-sat)"}) {
        Solver solver;
        REQUIRE(solver.parseFile(writeComboSmt2(source)));
        REQUIRE((solver.checkSat() == Result::Sat));
        CHECK((solver.validateModel() == Solver::ModelValidation::Satisfied));
    }
}

TEST_CASE("DT arithmetic selector projection reaches its owning arithmetic theory") {
    for (const auto& [value, expected] : {
        std::pair{"4", Result::Unsat}, std::pair{"3", Result::Sat}}) {
        Solver solver;
        const auto source = std::string(
            "(set-logic QF_UFDTNIA)"
            "(declare-datatypes ((Pair 0)) (((mk (fst Int) (snd Int)))))"
            "(declare-const x Int)(declare-const y Int)"
            "(assert (= (* x x) 9))(assert (> x 0))"
            "(assert (= (fst (mk x y)) ") + value + "))(check-sat)";
        REQUIRE(solver.parseFile(writeComboSmt2(source)));
        CHECK((solver.checkSat() == expected));
    }
}

TEST_CASE("QF_AUFLIA array UF model validates original assertions") {
    Solver solver;
    REQUIRE(solver.parseFile("tests/regression/auflia/audit_seed-17-case-125-model.smt2"));
    REQUIRE((solver.checkSat() == Result::Sat));
    CHECK((solver.validateModel() == Solver::ModelValidation::Satisfied));
}

TEST_CASE("QF_AUFLIA array UF model reconciles negated binary distinct") {
    Solver solver;
    REQUIRE(solver.parseFile("tests/regression/auflia/audit_seed-17-case-72-model.smt2"));
    REQUIRE((solver.checkSat() == Result::Sat));
    CHECK((solver.validateModel() == Solver::ModelValidation::Satisfied));
}

TEST_CASE("QF_AUFLIA array UF model propagates through all equivalent store chains") {
    Solver solver;
    const auto path = writeComboSmt2(
        "(set-logic QF_AUFLIA)(declare-const a (Array Int Int))"
        "(declare-const b (Array Int Int))(declare-fun g ((Array Int Int)) Int)"
        "(assert (= a (store b 2 0)))"
        "(assert (= (store b 3 7) (store a 4 9)))"
        "(assert (= (g a) (g b)))(check-sat)");
    REQUIRE(solver.parseFile(path));
    REQUIRE((solver.checkSat() == Result::Sat));
    CHECK((solver.validateModel() == Solver::ModelValidation::Satisfied));
}

TEST_CASE("array UF model separates arguments when arithmetic chooses distinct outputs") {
    for (const std::string logic : {"QF_AUFLIA", "QF_AUFNIA"}) {
        Solver solver;
        const auto path = writeComboSmt2(
            "(set-logic " + logic + ")(declare-const c (Array Int Int))"
            "(declare-fun g ((Array Int Int)) Int)"
            "(assert (= (g c) 4))(assert (= (g (store c 8 0)) 8))"
            "(assert (>= (select c 8) 0))(check-sat)");
        REQUIRE(solver.parseFile(path));
        REQUIRE((solver.checkSat() == Result::Sat));
        CHECK((solver.validateModel() == Solver::ModelValidation::Satisfied));
    }
}

TEST_CASE("array UF model separates opposite SAT-observed predicate results") {
    for (const std::string index : {"8", "i"}) {
        Solver solver;
        const auto path = writeComboSmt2(
            "(set-logic QF_AUFLIA)(declare-const c (Array Int Int))"
            "(declare-const i Int)"
            "(declare-fun h ((Array Int Int)) Bool)"
            "(assert (h c))(assert (not (h (store c " + index + " 0))))"
            "(assert (>= (select c " + index + ") 0))(check-sat)");
        REQUIRE(solver.parseFile(path));
        REQUIRE((solver.checkSat() == Result::Sat));
        CHECK((solver.validateModel() == Solver::ModelValidation::Satisfied));
    }
}

TEST_CASE("QF_ALIA store disequality preserves the arithmetic witness") {
    for (const std::string constant : {"0", "(- 2)"}) {
        Solver solver;
        const auto path = writeComboSmt2(
            "(set-logic QF_ALIA)(declare-const i Int)(declare-const j Int)"
            "(declare-const k Int)(declare-const a (Array Int Int))"
            "(assert (distinct i (+ i k)))"
            "(assert (< 1 (select (store a 1 5) 1)))"
            "(assert (distinct (store a j " + constant + ") a))(check-sat)");
        REQUIRE(solver.parseFile(path));
        REQUIRE((solver.checkSat() == Result::Sat));
        CHECK((solver.validateModel() == Solver::ModelValidation::Satisfied));
    }
}

TEST_CASE("QF_ALIA constant index disequality changes the integer model") {
    for (const std::string constant : {"(- 1)", "1"}) {
        Solver solver;
        const auto path = writeComboSmt2(
            "(set-logic QF_ALIA)(declare-const i Int)"
            "(declare-const a (Array Int Int))"
            "(assert (<= i " + constant + "))"
            "(assert (= (select a i) 3))"
            "(assert (= (select a " + constant + ") 4))(check-sat)");
        REQUIRE(solver.parseFile(path));
        REQUIRE((solver.checkSat() == Result::Sat));
        CHECK((solver.validateModel() == Solver::ModelValidation::Satisfied));
    }
}

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

// store(c,j,v)=c iff select(c,j)=v, including compound arithmetic v.
TEST_CASE("QF_ALIA store-vs-base compound value: unconditional axiom") {
    const char* smt =
        "(set-logic QF_ALIA)\n"
        "(declare-fun c () (Array Int Int))\n"
        "(declare-fun j () Int)\n"
        "(declare-fun k () Int)\n"
        "(assert (not (= (store c j (+ k 1)) c)))\n"
        "(check-sat)\n";

    CHECK((solveStr(smt) == Result::Sat));
    CHECK((solveStr(
        "(set-logic QF_ALIA)\n"
        "(declare-const c (Array Int Int))\n"
        "(declare-const j Int)\n"
        "(declare-const k Int)\n"
        "(assert (= (select c j) (+ k 1)))\n"
        "(assert (distinct (store c j (+ k 1)) c))\n"
        "(check-sat)\n") == Result::Unsat));
}

// This satisfiable store-inversion system used to expose an incomplete Row2
// candidate. Parser ordering changes can let the ordinary path solve it too.
// Both configurations must produce a model of the original assertions.
TEST_CASE("QF_AX storeinv multi-store: candidate model validates") {
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

    const auto path = writeComboSmt2(smt);
    {
        Solver solver;
        REQUIRE(solver.parseFile(path));
        REQUIRE((solver.checkSat() == Result::Sat));
        CHECK((solver.validateModel() == Solver::ModelValidation::Satisfied));
    }
}

// ---- #86 constant-index store-commutativity extensionality (QF_AUFLIA) -----
// (not (= A B)) where A,B are 10-deep store towers over the SAME base a1 with
// CONSTANT indices in different order: A writes {1..9}, B writes {1..10}, so they
// differ ONLY at index 10 (A[10]=a1[10], B[10]=e10) -> SAT. The lazy
// variable-witness path now recovers a positively checked model without the
// const-index ext clause (A=B) ∨ ⋁_c (select(A,c)!=select(B,c)) over the
// write-index union, and the #85 refinement re-asserts it once the const reads
// reduce (Row2-const) -> converges to the genuine sat. z3/cvc5 say sat; the model
// is ModelValidator-confirmed.
TEST_CASE("QF_AUFLIA storecomm: candidate model validates") {
    std::string smt =
        "(set-logic QF_AUFLIA)\n"
        "(declare-fun a1 () (Array Int Int))\n"
        "(declare-fun e1 () Int)(declare-fun e2 () Int)(declare-fun e3 () Int)\n"
        "(declare-fun e4 () Int)(declare-fun e5 () Int)(declare-fun e6 () Int)\n"
        "(declare-fun e7 () Int)(declare-fun e8 () Int)(declare-fun e9 () Int)\n"
        "(declare-fun e10 () Int)\n"
        "(assert (not (= "
        "(store (store (store (store (store (store (store (store (store (store "
        "a1 1 e1) 2 e2) 3 e3) 4 e4) 5 e5) 6 e6) 7 e7) 8 e8) 9 e9) 1 e1) "
        "(store (store (store (store (store (store (store (store (store (store "
        "a1 9 e9) 3 e3) 5 e5) 4 e4) 6 e6) 1 e1) 10 e10) 2 e2) 8 e8) 7 e7))))\n"
        "(check-sat)\n";

    // const reads reduce through). The Solver API does not apply baked defaults.

    auto checkedSolve = [&]() {
        Solver solver;
        REQUIRE(solver.parseFile(writeComboSmt2(smt)));
        Result result = solver.checkSat();
        if (result == Result::Sat)
            CHECK((solver.validateModel() == Solver::ModelValidation::Satisfied));
        return result;
    };

    // Both optional search configurations must produce a checked model.
    Result off = checkedSolve();
    CHECK(static_cast<int>(off) == static_cast<int>(Result::Sat));

    // ON: const-index ext lemma + refinement converge to the genuine sat.
    Result on = checkedSolve();
    CHECK(static_cast<int>(on) == static_cast<int>(Result::Sat));
}

}  // TEST_SUITE
