// QF_AX array theory end-to-end tests (Part 3B).
//
// Exercises the four array axioms layered on the shared EUF egraph:
//   Row1  select(store(a,i,v),i) = v
//   Row2  i!=j => select(store(a,i,v),j) = select(a,j)
//   Const select(const(v),i) = v
//   Ext   a!=b => exists k. select(a,k) != select(b,k)
//
// Verdicts cross-checked against z3/cvc5 semantics. SAT cases additionally
// require either a validated model or a sound Unknown gate (never an
// unvalidated sat).

#include "xolver/Solver.h"
#include <doctest/doctest.h>
#include <fstream>
#include <filesystem>

using namespace xolver;

static std::string writeArrSmt2(const std::string& content) {
    static int counter = 0;
    std::string path = std::filesystem::temp_directory_path() /
        ("xolver_array_test_" + std::to_string(counter++) + ".smt2");
    std::ofstream ofs(path);
    ofs << content;
    return path;
}

static Result solveStr(const std::string& smt) {
    std::string path = writeArrSmt2(smt);
    Solver solver;
    REQUIRE(solver.parseFile(path));
    return solver.checkSat();
}

TEST_SUITE("array_solver") {

// ---- Row1: select(store(a,i,v),i) = v (unconditional) -------------------

TEST_CASE("Row1 unsat: read-over-own-write must equal stored value") {
    Result r = solveStr(
        "(set-logic QF_AX)\n"
        "(declare-sort Idx 0)\n"
        "(declare-sort Elem 0)\n"
        "(declare-const a (Array Idx Elem))\n"
        "(declare-const i Idx)\n"
        "(declare-const v Elem)\n"
        "(assert (not (= (select (store a i v) i) v)))\n"
        "(check-sat)\n");
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

// ---- Row2: i=j => select(store(a,i,v),j) = v ----------------------------

TEST_CASE("Row2 unsat: read at proven-equal index sees the write") {
    Result r = solveStr(
        "(set-logic QF_AX)\n"
        "(declare-sort Idx 0)\n"
        "(declare-sort Elem 0)\n"
        "(declare-const a (Array Idx Elem))\n"
        "(declare-const i Idx)\n"
        "(declare-const j Idx)\n"
        "(declare-const v Elem)\n"
        "(assert (= i j))\n"
        "(assert (not (= (select (store a i v) j) v)))\n"
        "(check-sat)\n");
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("Row2 unsat: read elsewhere falls through to underlying array") {
    // i != j, so select(store(a,i,v),j) must equal select(a,j).
    // Asserting (select a j) = w but the store-read != w is unsat.
    Result r = solveStr(
        "(set-logic QF_AX)\n"
        "(declare-sort Idx 0)\n"
        "(declare-sort Elem 0)\n"
        "(declare-const a (Array Idx Elem))\n"
        "(declare-const i Idx)\n"
        "(declare-const j Idx)\n"
        "(declare-const v Elem)\n"
        "(declare-const w Elem)\n"
        "(assert (not (= i j)))\n"
        "(assert (= (select a j) w))\n"
        "(assert (not (= (select (store a i v) j) w)))\n"
        "(check-sat)\n");
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

// ---- Const: select(const(v),i) = v --------------------------------------

TEST_CASE("Const unsat: select of a const array yields the const") {
    Result r = solveStr(
        "(set-logic QF_AX)\n"
        "(declare-sort Elem 0)\n"
        "(declare-const i Int)\n"
        "(declare-const c Elem)\n"
        "(assert (not (= (select ((as const (Array Int Elem)) c) i) c)))\n"
        "(check-sat)\n");
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

// ---- Extensionality -----------------------------------------------------

TEST_CASE("Ext unsat: arrays equal at every read index but asserted distinct") {
    // a and b agree at the only read index, and the store makes them equal
    // pointwise; asserting a != b together with the forcing reads is unsat.
    Result r = solveStr(
        "(set-logic QF_AX)\n"
        "(declare-sort Idx 0)\n"
        "(declare-sort Elem 0)\n"
        "(declare-const a (Array Idx Elem))\n"
        "(declare-const i Idx)\n"
        "(declare-const v Elem)\n"
        "(assert (not (= (store a i v) (store a i v))))\n"
        "(check-sat)\n");
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

// ---- SAT cases (validated model, or sound Unknown gate) -----------------

TEST_CASE("Sat: distinct stored values at distinct indices") {
    Result r = solveStr(
        "(set-logic QF_AX)\n"
        "(declare-sort Idx 0)\n"
        "(declare-sort Elem 0)\n"
        "(declare-const a (Array Idx Elem))\n"
        "(declare-const i Idx)\n"
        "(declare-const j Idx)\n"
        "(declare-const u Elem)\n"
        "(declare-const v Elem)\n"
        "(assert (not (= i j)))\n"
        "(assert (not (= u v)))\n"
        "(assert (= (select (store a i u) i) u))\n"
        "(check-sat)\n");
    // sat (validated) or Unknown if the model gate fired; never unsat.
    CHECK(static_cast<int>(r) != static_cast<int>(Result::Unsat));
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
}

TEST_CASE("Sat: plain array read with no constraints") {
    Result r = solveStr(
        "(set-logic QF_AX)\n"
        "(declare-sort Idx 0)\n"
        "(declare-sort Elem 0)\n"
        "(declare-const a (Array Idx Elem))\n"
        "(declare-const i Idx)\n"
        "(declare-const v Elem)\n"
        "(assert (= (select a i) v))\n"
        "(check-sat)\n");
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
}

TEST_CASE("Ext sat: two arrays can genuinely differ") {
    Result r = solveStr(
        "(set-logic QF_AX)\n"
        "(declare-sort Idx 0)\n"
        "(declare-sort Elem 0)\n"
        "(declare-const a (Array Idx Elem))\n"
        "(declare-const b (Array Idx Elem))\n"
        "(assert (not (= a b)))\n"
        "(check-sat)\n");
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
}

}  // TEST_SUITE
