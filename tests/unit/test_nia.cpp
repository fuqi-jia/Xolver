#include <doctest/doctest.h>
#include "xolver/Solver.h"
#include <fstream>
#include <filesystem>
#include <cstdlib>

using namespace xolver;

static std::string writeTempSmt2(const std::string& content) {
    std::string path = std::filesystem::temp_directory_path() / "xolver_nia.smt2";
    std::ofstream ofs(path);
    ofs << content;
    return path;
}

TEST_CASE("NIA: trivial constant unsat (= 1 0)") {
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(assert (= 1 0))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("NIA: trivial constant sat (> 1 0)") {
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(assert (> 1 0))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
}

TEST_CASE("NIA: non-constant returns Unknown (= (* x x) 2)") {
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(assert (= (* x x) 2))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    // NIA-Core: UnivariateIntegerReasoner proves x^2=2 has no integer roots (UNSAT)
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("NIA: false literal negation (not (> 1 0)) -> unsat") {
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(assert (not (> 1 0)))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("NIA: distinct constant unsat (distinct 1 1)") {
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(assert (distinct 1 1))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("NIA: eq negation constant unsat (not (= 1 1))") {
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(assert (not (= 1 1)))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("NIA: non-integer rational constant returns Unsat") {
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(assert (= (/ 1 2) 0))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("NIA: linear atom goes through polynomial path -> Sat") {
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(assert (>= x 0))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    // Linear constraint x>=0 is satisfiable (e.g. x=0)
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
}

// ===========================================================================
// Category F: Strict inequality end-to-end
// ===========================================================================

TEST_CASE("NIA: strict Lt (< x 5) -> sat (x=4)") {
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(assert (< x 5))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
}

TEST_CASE("NIA: strict Gt (> x 0) -> sat (x=1)") {
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(assert (> x 0))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
}

TEST_CASE("NIA: strict Lt + Gt direct conflict (< x 3) + (> x 3) -> unsat") {
    // Normalizes to: x <= 2 and x >= 4 → direct empty-domain conflict
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(assert (< x 3))\n"
        "(assert (> x 3))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("NIA: strict nonlinear (< (* x x) 0) -> unsat") {
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(assert (< (* x x) 0))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

// ===========================================================================
// Category H: False literal effective relation regression
// ===========================================================================

TEST_CASE("NIA: false Leq effective relation (not (<= x 0)) + (<= x 0) -> unsat") {
    // not(x <= 0) means x > 0, which normalizes to x >= 1.
    // Together with x <= 0: direct empty-domain conflict.
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(assert (not (<= x 0)))\n"
        "(assert (<= x 0))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("NIA: false Geq effective relation (not (>= x 0)) + (>= x 0) -> unsat") {
    // not(x >= 0) means x < 0, which normalizes to x <= -1.
    // Together with x >= 0: direct empty-domain conflict.
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(assert (not (>= x 0)))\n"
        "(assert (>= x 0))\n"
        "(check-sat)\n"
    );

    Solver solver;
    solver.setLogic("QF_NIA");
    CHECK(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}

TEST_CASE("NIA linear-decide: combination linear SAT solved without bit-blast") {
    // Regression for the QF_ANIA SVCOMP cluster (UltimateAutomizer sum10/avg):
    // a purely-LINEAR array+NIA SAT formula whose model needs a value just above
    // 2^31 (mod-by-2^32). The array reads are unconstrained ⇒ free integer
    // bridge variables; the constraint forces their sum mod 2^32 to exceed
    // 2^31-1 (e.g. A[0]=2^31, A[1]=A[2]=0). The NIA pipeline's only complete
    // model-finder for this shape was bit-blast, which escalates bit-width and
    // times out in combination mode; with bit-blast disabled the remaining
    // stages return Unknown. The embedded-LIA linear-decide stage must DECIDE it
    // (exact, IntegerModelValidator-checked integer model) and return Sat.
    // bit-blast is disabled here to isolate the linear-decide path: without the
    // new stage this case returns `unknown`. The stage is opt-in (default-OFF)
    // until it nets positive on the broader cluster, so enable it explicitly.
    setenv("XOLVER_NIA_LINEAR_DECIDE", "1", 1);
    setenv("XOLVER_NIA_NO_BITBLAST", "1", 1);
    std::string path = writeTempSmt2(
        "(set-logic QF_ANIA)\n"
        "(declare-const A (Array Int Int))\n"
        "(declare-const r Int)\n"
        "(assert (= r (mod (+ (select A 0) (select A 1) (select A 2)) 4294967296)))\n"
        "(assert (> r 2147483647))\n"
        "(check-sat)\n"
    );
    Solver solver;
    solver.setLogic("QF_ANIA");
    REQUIRE(solver.parseFile(path));
    Result r = solver.checkSat();
    unsetenv("XOLVER_NIA_NO_BITBLAST");
    unsetenv("XOLVER_NIA_LINEAR_DECIDE");
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
}

TEST_CASE("NIA linear-decide: theory conflict prunes an infeasible branch (still SAT, never wrong-UNSAT)") {
    // The linear-decide stage feeds the embedded LIA the REAL asserted satVars,
    // so when a bool assignment makes the linear part infeasible (the `!b` branch
    // x=5 ∧ x=6), the embedded LIA's Farkas conflict — over those real literals —
    // is returned as a theory conflict that PRUNES that branch. SAT then takes the
    // `b` branch (a large-valued mod goal) which linear-decide solves with a
    // model. Net: SAT (NOT unsat — the conflict must never escalate to a global
    // UNSAT on a satisfiable formula; that is the cardinal-sin guard).
    setenv("XOLVER_NIA_LINEAR_DECIDE", "1", 1);
    setenv("XOLVER_NIA_NO_BITBLAST", "1", 1);
    std::string path = writeTempSmt2(
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(declare-const y Int)\n"
        "(declare-const b Bool)\n"
        "(assert (ite b\n"
        "  (< 2147483647 (mod (+ x y) 4294967296))\n"
        "  (and (= x 5) (= x 6))))\n"
        "(check-sat)\n"
    );
    Solver solver;
    solver.setLogic("QF_NIA");
    REQUIRE(solver.parseFile(path));
    Result r = solver.checkSat();
    unsetenv("XOLVER_NIA_NO_BITBLAST");
    unsetenv("XOLVER_NIA_LINEAR_DECIDE");
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Sat));
}
