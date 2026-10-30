// Public SMT2 regressions for integer arithmetic and the retained NRA MCSAT backend.
// NRA MCSAT must agree with the expected answer or return Unknown.

#include <doctest/doctest.h>
#include <xolver/Result.h>
#include <xolver/Solver.h>
#include "frontend/parser/adapter.h"
#include "search/boolean/Atomizer.h"
#include "search/coordination/TheoryManager.h"
#include "search/coordination/TheoryAtomRegistry.h"
#include "search/coordination/TheoryLemmaDatabase.h"
#include "search/sat/CadicalBackend.h"
#include "search/sat/CadicalTheoryPropagator.h"
#include "applications/satisfiability/smt/qfnra/McsatSolver.h"
#include "search/nra/backend/LibpolyBackend.h"
#include "search/nra/engine/NlsatEngine.h"

#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <string>
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
    // Exercise the selected theory through the real parser, atomizer and SAT
    // callbacks. Runtime preprocessing can now prove UNSAT before constructing
    // any theory stack; using it here would leave the backend test vacuous.
    SOMTParser::Parser parser;
    REQUIRE(parser.parseStr(text));
    FrontendAdapter adapter(parser);
    auto terms = adapter.importProblem(false);
    auto sat = createSatSolver();
    auto& backend = dynamic_cast<CadicalBackend&>(*sat);
    TheoryAtomRegistry registry;
    TheoryManager theories;
    TheoryLemmaDatabase lemmas;
    auto kernel = createPolynomialKernel();
    auto* polynomialKernel = kernel.get();
    auto algebra = std::make_unique<LibpolyBackend>(polynomialKernel);
    auto engine = std::make_unique<nlsat::NlsatEngine>();
    engine->setAlgebra(polynomialKernel, algebra.get());
    engine->setNativeTerms(terms.get());
    struct TrackedMcsat : McsatSolver {
        size_t checks = 0;
        TheoryCheckResult check(TheoryLemmaStorage& db, TheoryEffort effort) override {
            ++checks;
            return McsatSolver::check(db, effort);
        }
    };
    auto mcsat = std::make_unique<TrackedMcsat>();
    auto* tracked = mcsat.get();
    mcsat->setEngine(std::move(engine), TheoryId::NRA);
    mcsat->setKernel(std::move(kernel));
    mcsat->setAlgebra(std::move(algebra));
    theories.registerSolver(std::move(mcsat));
    theories.setRegistry(&registry);
    CadicalTheoryPropagator propagator(registry, theories, lemmas, backend);
    backend.connectPropagator(&propagator);
    struct Disconnect {
        CadicalBackend& backend;
        ~Disconnect() { backend.disconnectPropagator(); }
    } disconnect{backend};
    Atomizer atomizer(*sat);
    registry.setContext(sat.get(), &atomizer);
    atomizer.setRegistry(&registry);
    atomizer.setBoolSortId(adapter.getBoolSortId());
    atomizer.setDefaultTheory(TheoryId::NRA);
    atomizer.setPolynomialKernel(polynomialKernel);
    for (auto root : terms->assertions()) sat->addClause({atomizer.atomize(root, *terms)});
    sat->setDeadline(std::chrono::steady_clock::now() + std::chrono::seconds(5));
    const auto result = sat->solve();
    REQUIRE(tracked->checks > 0);
    if (result == SatSolver::SolveResult::Unsat) return Result::Unsat;
    if (result == SatSolver::SolveResult::Sat) return Result::Sat;
    return Result::Unknown;
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
