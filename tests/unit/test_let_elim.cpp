// ZOLVER_PP_LET_ELIM: import-time elimination of residual let nodes.
//
// SOMTParser preserves lets and its expandLet only expands the outermost one,
// so a let nested in a binding VALUE or an operand position survives as a
// let_chain that the adapter cannot map (-> Kind::Unknown -> unknown verdict),
// blocking let-heavy QF_ALIA/AUFLIA (Ultimate-Automizer SV-COMP) cases. With
// the flag, the adapter substitutes by node identity (a let_bind_var IS its
// value, a let/let_chain IS its body), collapsing arbitrary nesting in one
// pass. Verdicts here are cross-checked against z3 (capture-safety included).
#include <doctest/doctest.h>
#include "zolver/Solver.h"
#include <cstdlib>
#include <fstream>
#include <filesystem>
#include <string>

using namespace zolver;

namespace {
struct LetElimEnv {
    LetElimEnv()  { setenv("ZOLVER_PP_LET_ELIM", "1", 1); }
    ~LetElimEnv() { unsetenv("ZOLVER_PP_LET_ELIM"); }
};
Result solveStr(const std::string& smt, const std::string& tag) {
    std::string path = (std::filesystem::temp_directory_path() /
                        ("zolver_let_" + tag + ".smt2")).string();
    { std::ofstream(path) << smt; }
    Solver s;
    REQUIRE(s.parseFile(path));
    return s.checkSat();
}
} // namespace

TEST_CASE("let-elim: nested let in a binding value recovers (z3=sat)") {
    LetElimEnv guard;
    // a = (c+c) where c = x+1  ->  2x+2 = 4  ->  x=1.
    CHECK(static_cast<int>(solveStr(
        "(set-logic QF_LIA)(declare-const x Int)"
        "(assert (let ((a (let ((c (+ x 1))) (+ c c)))) (= a 4)))(check-sat)\n", "val"))
        == static_cast<int>(Result::Sat));
}

TEST_CASE("let-elim: lets in operand positions recover (z3=sat)") {
    LetElimEnv guard;
    CHECK(static_cast<int>(solveStr(
        "(set-logic QF_LIA)(declare-const x Int)"
        "(assert (= 4 (+ (let ((c (+ x 1))) c) (let ((d (+ x 1))) d))))(check-sat)\n", "arg"))
        == static_cast<int>(Result::Sat));
}

TEST_CASE("let-elim: nested-let contradiction stays unsat (z3=unsat)") {
    LetElimEnv guard;
    CHECK(static_cast<int>(solveStr(
        "(set-logic QF_LIA)(declare-const x Int)"
        "(assert (let ((a (let ((c (+ x 1))) (+ c c)))) (and (= a 4) (= a 5))))(check-sat)\n", "C"))
        == static_cast<int>(Result::Unsat));
}

TEST_CASE("let-elim: variable shadowing is capture-safe (z3=sat)") {
    LetElimEnv guard;
    // Inner c = 2x shadows outer c = x+1 inside d's value; the body's `c` is the
    // outer one. d = 2x+1 = 7 -> x=3, and outer c = x+1 = 4 holds. Capture would
    // give a wrong answer; node-identity binding does not.
    CHECK(static_cast<int>(solveStr(
        "(set-logic QF_LIA)(declare-const x Int)"
        "(assert (let ((c (+ x 1))) (let ((d (let ((c (* x 2))) (+ c 1))))"
        "  (and (= d 7) (= c (+ x 1))))))(check-sat)\n", "shadow"))
        == static_cast<int>(Result::Sat));
}

TEST_CASE("let-elim: let-bound array index (QF_ALIA target, z3=sat)") {
    LetElimEnv guard;
    CHECK(static_cast<int>(solveStr(
        "(set-logic QF_ALIA)(declare-fun A () (Array Int Int))(declare-const x Int)"
        "(assert (let ((i (+ x 1))) (= (select (store A i 5) i) 5)))(check-sat)\n", "arr"))
        == static_cast<int>(Result::Sat));
}

TEST_CASE("let-elim: flag OFF leaves the residual-let gap (unknown), unchanged") {
    // Without the flag, the nested let in a binding value is still unmapped ->
    // unknown. This pins the gate: the fix is opt-in, default behavior intact.
    CHECK(static_cast<int>(solveStr(
        "(set-logic QF_LIA)(declare-const x Int)"
        "(assert (let ((a (let ((c (+ x 1))) (+ c c)))) (= a 4)))(check-sat)\n", "off"))
        == static_cast<int>(Result::Unknown));
}
