// Algebraic-datatype theory end-to-end tests (QF_UFDT / QF_UFDTNIA).
//
// Exercises the lazy DT axioms layered on the shared EUF egraph:
//   clash         C(..) = D(..), C != D            -> UNSAT
//   injectivity   C(a..) = C(b..) => a_i = b_i      -> UNSAT with a_i != b_i
//   projection    sel_i^C(C(a..)) = a_i (guarded)   -> UNSAT
//   acyclicity    x = C(... x ...) (recursive)      -> UNSAT
//
// Soundness invariants checked here:
//   * Guarded selectors: head(nil) is underspecified, NEVER a conflict
//     (the result must NOT be Unsat).
//   * DT-logic sat is floored to Unknown (sound), so satisfiable cases must
//     also be NOT Unsat.

#include "xolver/Solver.h"
#include <doctest/doctest.h>
#include <fstream>
#include <filesystem>

using namespace xolver;

static std::string writeDtSmt2(const std::string& content) {
    static int counter = 0;
    std::string path = std::filesystem::temp_directory_path() /
        ("xolver_dt_test_" + std::to_string(counter++) + ".smt2");
    std::ofstream ofs(path);
    ofs << content;
    return path;
}

static Result solveDt(const std::string& smt) {
    std::string path = writeDtSmt2(smt);
    Solver solver;
    REQUIRE(solver.parseFile(path));
    return solver.checkSat();
}

TEST_SUITE("datatype_solver") {

// ---- Constructor clash --------------------------------------------------

TEST_CASE("clash: distinct enum constructors are disjoint -> unsat") {
    Result r = solveDt(
        "(set-logic QF_UFDT)\n"
        "(declare-datatypes ((Color 0)) (((red) (green) (blue))))\n"
        "(declare-const x Color)\n"
        "(assert (= x red))\n"
        "(assert (= x green))\n"
        "(check-sat)\n");
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

// ---- Injectivity --------------------------------------------------------

TEST_CASE("injectivity: box(p)=box(q) forces p=q -> unsat with p!=q") {
    Result r = solveDt(
        "(set-logic QF_UFDT)\n"
        "(declare-datatypes ((Color 0)) (((red) (green) (blue))))\n"
        "(declare-datatypes ((Box 0)) (((box (item Color)))))\n"
        "(declare-const p Color)\n"
        "(declare-const q Color)\n"
        "(assert (= (box p) (box q)))\n"
        "(assert (not (= p q)))\n"
        "(check-sat)\n");
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

// ---- Guarded selector projection ----------------------------------------

TEST_CASE("projection: fst(mk(a,b)) = a -> unsat when fst(p)!=a") {
    Result r = solveDt(
        "(set-logic QF_UFDT)\n"
        "(declare-datatypes ((Color 0)) (((red) (green) (blue))))\n"
        "(declare-datatypes ((Pair 0)) (((mk (fst Color) (snd Color)))))\n"
        "(declare-const a Color)\n"
        "(declare-const b Color)\n"
        "(declare-const p Pair)\n"
        "(assert (= p (mk a b)))\n"
        "(assert (not (= (fst p) a)))\n"
        "(check-sat)\n");
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

// ---- Acyclicity (recursive datatype) ------------------------------------

TEST_CASE("acyclicity: x = cons(h,x) is cyclic -> unsat") {
    Result r = solveDt(
        "(set-logic QF_UFDT)\n"
        "(declare-datatypes ((Color 0)) (((red) (green) (blue))))\n"
        "(declare-datatypes ((Lst 0)) (((cons (head Color) (tail Lst)) (nil))))\n"
        "(declare-const x Lst)\n"
        "(declare-const h Color)\n"
        "(assert (= x (cons h x)))\n"
        "(check-sat)\n");
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

// ---- Soundness: guarded selector is NOT a conflict ----------------------

TEST_CASE("guarded selector sat: head(nil)=red is satisfiable (determined model)") {
    Result r = solveDt(
        "(set-logic QF_UFDT)\n"
        "(declare-datatypes ((Color 0)) (((red) (green) (blue))))\n"
        "(declare-datatypes ((Lst 0)) (((cons (head Color) (tail Lst)) (nil))))\n"
        "(declare-const x Lst)\n"
        "(assert (= x nil))\n"
        "(assert (= (head x) red))\n"
        "(check-sat)\n");
    // head(nil) is underspecified, can be red; every datatype class is
    // constructor-determined (x=nil, head(x)=red) -> sound sat. Never Unsat.
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
}

// ---- Satisfiable enum choice (determined model) -------------------------

TEST_CASE("sat enum choice: x in {red,green}, x!=blue is satisfiable") {
    Result r = solveDt(
        "(set-logic QF_UFDT)\n"
        "(declare-datatypes ((Color 0)) (((red) (green) (blue))))\n"
        "(declare-const x Color)\n"
        "(assert (or (= x red) (= x green)))\n"
        "(assert (not (= x blue)))\n"
        "(check-sat)\n");
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
}

// ---- Exhaustiveness split (tier-3) recovery ------------------------------

TEST_CASE("finite cardinality: 4 distinct over 3-constructor enum -> unsat") {
    Result r = solveDt(
        "(set-logic QF_UFDT)\n"
        "(declare-datatypes ((Color 0)) (((red) (green) (blue))))\n"
        "(declare-const a Color)(declare-const b Color)\n"
        "(declare-const c Color)(declare-const d Color)\n"
        "(assert (distinct a b c d))\n"
        "(check-sat)\n");
    // Pigeonhole: refuted by per-branch constructor split + clash.
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("selector split: head(x)=red with unknown ctor is sat (split)") {
    Result r = solveDt(
        "(set-logic QF_UFDT)\n"
        "(declare-datatypes ((Color 0)) (((red) (green) (blue))))\n"
        "(declare-datatypes ((Lst 0)) (((cons (head Color) (tail Lst)) (nil))))\n"
        "(declare-const x Lst)\n"
        "(assert (= (head x) red))\n"
        "(check-sat)\n");
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
}

TEST_CASE("tester reconstruct: is_cons(x) and head(x)=red is sat") {
    Result r = solveDt(
        "(set-logic QF_UFDT)\n"
        "(declare-datatypes ((Color 0)) (((red) (green) (blue))))\n"
        "(declare-datatypes ((Lst 0)) (((cons (head Color) (tail Lst)) (nil))))\n"
        "(declare-const x Lst)\n"
        "(assert ((_ is cons) x))\n"
        "(assert (= (head x) red))\n"
        "(check-sat)\n");
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
}

TEST_CASE("free infinite vars: distinct lists is sat without splitting") {
    Result r = solveDt(
        "(set-logic QF_UFDT)\n"
        "(declare-datatypes ((Color 0)) (((red) (green) (blue))))\n"
        "(declare-datatypes ((Lst 0)) (((cons (head Color) (tail Lst)) (nil))))\n"
        "(declare-const x Lst)(declare-const y Lst)\n"
        "(assert (distinct x y))\n"
        "(check-sat)\n");
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
}

} // TEST_SUITE
