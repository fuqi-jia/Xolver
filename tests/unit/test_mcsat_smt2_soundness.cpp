// Public SMT2 regressions for integer arithmetic and the retained NRA MCSAT backend.
// NRA MCSAT must agree with the expected answer or return Unknown.

#include <doctest/doctest.h>
#include <xolver/Result.h>
#include <xolver/Solver.h>
#include "runtime/factory/SolverRegistry.h"
#include "search/coordination/TheoryManager.h"
#include "search/experimental/mcsat/McsatSolver.h"
#include "search/nra/backend/LibpolyBackend.h"
#include "search/nra/engine/NlsatEngine.h"
#include "search/lra/LraSolver.h"

#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <string>
#include <cerrno>
#include <sys/wait.h>
#include <unistd.h>

using namespace xolver;

namespace {

// Write an SMT2 file; solveSmt2 removes it immediately after parsing.
std::string writeTempSmt2(const std::string& text) {
    char path[] = "/tmp/xolver_mcsat_smt2_XXXXXX.smt2";
    int fd = mkstemps(path, 5);
    REQUIRE(fd >= 0);
    std::string asStr(path);
    std::ofstream out(asStr);
    out << text;
    out.close();
    close(fd);
    return asStr;
}

Result solveSmt2(const std::string& text) {
    auto path = writeTempSmt2(text);
    Solver s;
    bool parsed = s.parseFile(path);
    std::remove(path.c_str());
    if (!parsed) return Result::Unknown;
    return s.checkSat();
}

Result solveSmt2WithMcsat(const std::string& text) {
    // The existing builder interface connects the experimental backend in this
    // test only. A child process isolates the registry override from all other
    // tests, without adding a production option or mutating the environment.
    pid_t child = fork();
    REQUIRE(child >= 0);
    if (child == 0) {
        bool built = false;
        SolverRegistry::ensureBuiltinsRegistered();
        SolverRegistry::registerLogic({"QF_NRA"}, 100, [&](BuildContext& c) {
            built = true;
            auto kernel = createPolynomialKernel();
            c.result->polyKernelRaw = kernel.get();
            auto algebra = std::make_unique<LibpolyBackend>(kernel.get());
            auto engine = std::make_unique<nlsat::NlsatEngine>();
            engine->setAlgebra(kernel.get(), algebra.get());
            engine->setNativeTerms(c.ir);
            auto mcsat = std::make_unique<McsatSolver>();
            mcsat->setEngine(std::move(engine), TheoryId::NRA);
            mcsat->setKernel(std::move(kernel));
            mcsat->setAlgebra(std::move(algebra));
            c.theoryManager->registerSolver(std::move(mcsat));
            auto lra = std::make_unique<LraSolver>();
            lra->setRegistry(c.registry);
            c.theoryManager->registerSolver(std::move(lra));
        }, "test-mcsat");
        Result result = solveSmt2(text);
        // Reject a vacuous test that never reached the experimental backend.
        _exit(built ? 10 + static_cast<int>(result) : 99);
    }
    int status = 0;
    pid_t waited;
    do { waited = waitpid(child, &status, 0); } while (waited < 0 && errno == EINTR);
    REQUIRE(waited == child);
    REQUIRE(WIFEXITED(status));
    const int code = WEXITSTATUS(status) - 10;
    REQUIRE(code >= static_cast<int>(Result::Sat));
    REQUIRE(code <= static_cast<int>(Result::Unknown));
    return static_cast<Result>(code);
}

// One-direction soundness gate. The "true" verdict comes from the
// baseline; the experimental path must agree OR be Unknown — never the
// opposite verdict.
void checkSoundWithMcsat(const std::string& smt2,
                         Result expectedBaseline) {
    Result baseline = solveSmt2(smt2);
    CHECK(static_cast<int>(baseline) == static_cast<int>(expectedBaseline));
    Result mcsat = solveSmt2WithMcsat(smt2);
    // MCSAT path must NOT contradict baseline.
    bool mcsatNotWrongUnsat = static_cast<int>(mcsat) != static_cast<int>(Result::Unsat)
                              || static_cast<int>(baseline) != static_cast<int>(Result::Sat);
    bool mcsatNotWrongSat = static_cast<int>(mcsat) != static_cast<int>(Result::Sat)
                            || static_cast<int>(baseline) != static_cast<int>(Result::Unsat);
    CHECK(mcsatNotWrongUnsat);
    CHECK(mcsatNotWrongSat);
}

} // namespace

TEST_CASE("MCSAT SMT2: x>=0 with a nonlinear companion reaches MCSAT (sat)") {
    std::string s =
        "(set-logic QF_NRA)\n"
        "(declare-fun x () Real)\n"
        "(declare-fun y () Real)\n"
        "(assert (= (* y y) 4))\n"
        "(assert (>= x 0))\n"
        "(check-sat)\n";
    checkSoundWithMcsat(s, Result::Sat);
}

TEST_CASE("MCSAT SMT2: x<0 and x>0 with a nonlinear companion must not report sat") {
    std::string s =
        "(set-logic QF_NRA)\n"
        "(declare-fun x () Real)\n"
        "(declare-fun y () Real)\n"
        "(assert (= (* y y) 4))\n"
        "(assert (< x 0))\n"
        "(assert (> x 0))\n"
        "(check-sat)\n";
    checkSoundWithMcsat(s, Result::Unsat);
}

TEST_CASE("MCSAT SMT2: QF_NRA x*x = 4 (sat) — baseline sat, MCSAT sat or unknown") {
    std::string s =
        "(set-logic QF_NRA)\n"
        "(declare-fun x () Real)\n"
        "(assert (= (* x x) 4))\n"
        "(check-sat)\n";
    checkSoundWithMcsat(s, Result::Sat);
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
    Result mcsat = solveSmt2WithMcsat(s);
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
    Result mcsat = solveSmt2WithMcsat(s);
    CHECK((static_cast<int>(mcsat) == static_cast<int>(Result::Unsat) || static_cast<int>(mcsat) == static_cast<int>(Result::Unknown)));
}

TEST_CASE("NIA SMT2: QF_NIA x>=0 (sat)") {
    std::string s =
        "(set-logic QF_NIA)\n"
        "(declare-fun x () Int)\n"
        "(assert (>= x 0))\n"
        "(check-sat)\n";
    CHECK(static_cast<int>(solveSmt2(s)) == static_cast<int>(Result::Sat));
}

TEST_CASE("NIA SMT2: QF_NIA x*x = 4 (sat)") {
    std::string s =
        "(set-logic QF_NIA)\n"
        "(declare-fun x () Int)\n"
        "(assert (= (* x x) 4))\n"
        "(check-sat)\n";
    CHECK(static_cast<int>(solveSmt2(s)) == static_cast<int>(Result::Sat));
}

TEST_CASE("NIA SMT2: QF_NIA x = 10 (sat)") {
    std::string s =
        "(set-logic QF_NIA)\n"
        "(declare-fun x () Int)\n"
        "(assert (= x 10))\n"
        "(check-sat)\n";
    CHECK(static_cast<int>(solveSmt2(s)) == static_cast<int>(Result::Sat));
}

TEST_CASE("NIA SMT2: QF_NIA x*x + 1 = 0 (unsat)") {
    std::string s =
        "(set-logic QF_NIA)\n"
        "(declare-fun x () Int)\n"
        "(assert (= (+ (* x x) 1) 0))\n"
        "(check-sat)\n";
    Result baseline = solveSmt2(s);
    CHECK(static_cast<int>(baseline) == static_cast<int>(Result::Unsat));
}

TEST_CASE("NIA SMT2: QF_NIA x > 0 AND x < 0 (unsat)") {
    std::string s =
        "(set-logic QF_NIA)\n"
        "(declare-fun x () Int)\n"
        "(assert (> x 0))\n"
        "(assert (< x 0))\n"
        "(check-sat)\n";
    Result baseline = solveSmt2(s);
    CHECK(static_cast<int>(baseline) == static_cast<int>(Result::Unsat));
}
