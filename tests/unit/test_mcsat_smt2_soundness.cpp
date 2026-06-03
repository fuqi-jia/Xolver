// SMT2 soundness gate for the MCSAT path through the public Solver API.
//
// For each curated SMT2 input we run the solver TWICE: once with the
// XOLVER_NRA_MCSAT / XOLVER_NIA_MCSAT flag OFF (baseline), once with the
// flag ON (MCSAT path). The framework allows two acceptable outcomes
// under the MCSAT flag:
//
//   - the same answer as baseline (best case), or
//   - Unknown (the soundness floor: MCSAT's engine couldn't decide,
//     so it bails to Unknown rather than guess).
//
// What is NEVER acceptable: the OPPOSITE of the true verdict. That is
// the wrong-answer case the MCSAT soundness floor (§15) exists to rule
// out. We assert this explicitly with a strict CHECK per case.

#include <doctest/doctest.h>
#include <xolver/Result.h>
#include <xolver/Solver.h>

#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <string>

using namespace xolver;

namespace {

// RAII guard: set an env var on construction, unset on destruction.
// TheoryFactory reads getenv() at setup time, so the guard must be in
// scope before the Solver constructor runs.
class EnvGuard {
public:
    EnvGuard(const char* name, const char* value) : name_(name) {
        setenv(name_, value, /*overwrite=*/1);
    }
    ~EnvGuard() { unsetenv(name_); }
    EnvGuard(const EnvGuard&) = delete;
    EnvGuard& operator=(const EnvGuard&) = delete;
private:
    const char* name_;
};

// Write `text` to a fresh temp file and return its path. The path
// stays valid for the test's lifetime (we just leak it — /tmp is small
// and these are tests).
std::string writeTempSmt2(const std::string& text) {
    char path[] = "/tmp/xolver_mcsat_smt2_XXXXXX";
    int fd = mkstemp(path);
    REQUIRE(fd >= 0);
    std::string asStr(path);
    asStr += ".smt2";
    std::ofstream out(asStr);
    out << text;
    out.close();
    close(fd);
    return asStr;
}

Result solveSmt2(const std::string& text) {
    auto path = writeTempSmt2(text);
    Solver s;
    if (!s.parseFile(path)) return Result::Unknown;
    return s.checkSat();
}

Result solveSmt2WithFlag(const std::string& text, const char* flag) {
    EnvGuard guard(flag, "1");
    return solveSmt2(text);
}

// One-direction soundness gate. The "true" verdict comes from the
// baseline; the flag-on path must agree OR be Unknown — never the
// opposite verdict.
void checkSoundUnderFlag(const std::string& smt2,
                         const char* flag,
                         Result expectedBaseline) {
    Result baseline = solveSmt2(smt2);
    CHECK(static_cast<int>(baseline) == static_cast<int>(expectedBaseline));
    Result mcsat = solveSmt2WithFlag(smt2, flag);
    // MCSAT path must NOT contradict baseline.
    bool mcsatNotWrongUnsat = static_cast<int>(mcsat) != static_cast<int>(Result::Unsat)
                              || static_cast<int>(baseline) != static_cast<int>(Result::Sat);
    bool mcsatNotWrongSat = static_cast<int>(mcsat) != static_cast<int>(Result::Sat)
                            || static_cast<int>(baseline) != static_cast<int>(Result::Unsat);
    CHECK(mcsatNotWrongUnsat);
    CHECK(mcsatNotWrongSat);
}

} // namespace

TEST_CASE("MCSAT SMT2: QF_NRA x>=0 (sat) — both baseline and MCSAT agree") {
    std::string s =
        "(set-logic QF_NRA)\n"
        "(declare-fun x () Real)\n"
        "(assert (>= x 0))\n"
        "(check-sat)\n";
    checkSoundUnderFlag(s, "XOLVER_NRA_MCSAT", Result::Sat);
}

TEST_CASE("MCSAT SMT2: QF_NRA x<0 ∧ x>0 (unsat) — MCSAT must NOT report sat") {
    std::string s =
        "(set-logic QF_NRA)\n"
        "(declare-fun x () Real)\n"
        "(assert (< x 0))\n"
        "(assert (> x 0))\n"
        "(check-sat)\n";
    checkSoundUnderFlag(s, "XOLVER_NRA_MCSAT", Result::Unsat);
}

TEST_CASE("MCSAT SMT2: QF_NRA x*x = 4 (sat) — baseline sat, MCSAT sat or unknown") {
    std::string s =
        "(set-logic QF_NRA)\n"
        "(declare-fun x () Real)\n"
        "(assert (= (* x x) 4))\n"
        "(check-sat)\n";
    checkSoundUnderFlag(s, "XOLVER_NRA_MCSAT", Result::Sat);
}

TEST_CASE("MCSAT SMT2: QF_NRA x*x = 5 (sat, irrational) — MCSAT must NOT report unsat") {
    std::string s =
        "(set-logic QF_NRA)\n"
        "(declare-fun x () Real)\n"
        "(assert (= (* x x) 5))\n"
        "(check-sat)\n";
    // Baseline knows the answer (√5); MCSAT only has rational candidates,
    // so it will bail to unknown — the soundness contract.
    Result baseline = solveSmt2(s);
    CHECK(static_cast<int>(baseline) == static_cast<int>(Result::Sat));
    Result mcsat = solveSmt2WithFlag(s, "XOLVER_NRA_MCSAT");
    CHECK((static_cast<int>(mcsat) == static_cast<int>(Result::Sat) || static_cast<int>(mcsat) == static_cast<int>(Result::Unknown)));
}

TEST_CASE("MCSAT SMT2: QF_NRA x*x = -1 (unsat) — MCSAT must NOT report sat") {
    std::string s =
        "(set-logic QF_NRA)\n"
        "(declare-fun x () Real)\n"
        "(assert (= (* x x) (- 1)))\n"
        "(check-sat)\n";
    Result baseline = solveSmt2(s);
    CHECK(static_cast<int>(baseline) == static_cast<int>(Result::Unsat));
    Result mcsat = solveSmt2WithFlag(s, "XOLVER_NRA_MCSAT");
    CHECK((static_cast<int>(mcsat) == static_cast<int>(Result::Unsat) || static_cast<int>(mcsat) == static_cast<int>(Result::Unknown)));
}

TEST_CASE("MCSAT SMT2: QF_NIA x>=0 (sat)") {
    std::string s =
        "(set-logic QF_NIA)\n"
        "(declare-fun x () Int)\n"
        "(assert (>= x 0))\n"
        "(check-sat)\n";
    checkSoundUnderFlag(s, "XOLVER_NIA_MCSAT", Result::Sat);
}

TEST_CASE("MCSAT SMT2: QF_NIA x*x = 4 (sat)") {
    std::string s =
        "(set-logic QF_NIA)\n"
        "(declare-fun x () Int)\n"
        "(assert (= (* x x) 4))\n"
        "(check-sat)\n";
    checkSoundUnderFlag(s, "XOLVER_NIA_MCSAT", Result::Sat);
}

TEST_CASE("MCSAT SMT2: QF_NIA x = 10 (sat)") {
    std::string s =
        "(set-logic QF_NIA)\n"
        "(declare-fun x () Int)\n"
        "(assert (= x 10))\n"
        "(check-sat)\n";
    checkSoundUnderFlag(s, "XOLVER_NIA_MCSAT", Result::Sat);
}

TEST_CASE("MCSAT SMT2: QF_NIA x*x + 1 = 0 (unsat) — MCSAT must NOT report sat") {
    std::string s =
        "(set-logic QF_NIA)\n"
        "(declare-fun x () Int)\n"
        "(assert (= (+ (* x x) 1) 0))\n"
        "(check-sat)\n";
    Result baseline = solveSmt2(s);
    CHECK(static_cast<int>(baseline) == static_cast<int>(Result::Unsat));
    Result mcsat = solveSmt2WithFlag(s, "XOLVER_NIA_MCSAT");
    CHECK((static_cast<int>(mcsat) == static_cast<int>(Result::Unsat) || static_cast<int>(mcsat) == static_cast<int>(Result::Unknown)));
}

TEST_CASE("MCSAT SMT2: QF_NIA x > 0 AND x < 0 (unsat)") {
    std::string s =
        "(set-logic QF_NIA)\n"
        "(declare-fun x () Int)\n"
        "(assert (> x 0))\n"
        "(assert (< x 0))\n"
        "(check-sat)\n";
    Result baseline = solveSmt2(s);
    CHECK(static_cast<int>(baseline) == static_cast<int>(Result::Unsat));
    Result mcsat = solveSmt2WithFlag(s, "XOLVER_NIA_MCSAT");
    CHECK((static_cast<int>(mcsat) == static_cast<int>(Result::Unsat) || static_cast<int>(mcsat) == static_cast<int>(Result::Unknown)));
}
