// XOLVER_STRAT_PORTFOLIO: ordered strategy arms tried until one returns a
// definitive verdict. Phase 1 is a single base arm (== XOLVER_STRAT_PRESETS),
// so a portfolio run is behavior-neutral. The multi-arm executor is exercised
// via the XOLVER_STRAT_PORTFOLIO_TEST_ARMS test hook, which replicates the base
// arm N times: running an IDENTICAL arm N times must not change the verdict,
// which proves the per-arm pristine re-entry (reset + re-parse) is sound.
#include <doctest/doctest.h>
#include "xolver/Solver.h"
#include "frontend/factory/StrategyPresets.h"
#include "theory/core/LogicFeatureDetector.h"
#include <cstdlib>
#include <fstream>
#include <filesystem>
#include <string>

using namespace xolver;

namespace {
struct PortfolioEnv {
    explicit PortfolioEnv(int armsN) {
        setenv("XOLVER_STRAT_PORTFOLIO", "1", 1);
        if (armsN > 1) setenv("XOLVER_STRAT_PORTFOLIO_TEST_ARMS",
                              std::to_string(armsN).c_str(), 1);
    }
    ~PortfolioEnv() {
        unsetenv("XOLVER_STRAT_PORTFOLIO");
        unsetenv("XOLVER_STRAT_PORTFOLIO_TEST_ARMS");
    }
};
struct BudgetEnv {
    explicit BudgetEnv(int budgetMs) {
        setenv("XOLVER_STRAT_PORTFOLIO", "1", 1);
        setenv("XOLVER_STRAT_PORTFOLIO_BUDGET_MS",
               std::to_string(budgetMs).c_str(), 1);
    }
    ~BudgetEnv() {
        unsetenv("XOLVER_STRAT_PORTFOLIO");
        unsetenv("XOLVER_STRAT_PORTFOLIO_BUDGET_MS");
    }
};
Result solveFile(const std::string& smt, const std::string& tag) {
    std::string path = (std::filesystem::temp_directory_path() /
                        ("xolver_pf_" + tag + ".smt2")).string();
    { std::ofstream(path) << smt; }
    Solver s;
    REQUIRE(s.parseFile(path));
    return s.checkSat();
}
} // namespace

TEST_CASE("portfolio: selectPortfolio always returns a base arm") {
    LogicFeatures f{};
    auto arms = selectPortfolio("QF_LIA", f);
    REQUIRE(arms.size() >= 1);
    CHECK(arms[0].label == "base");
    // The base arm mirrors selectStrategy exactly.
    CHECK(arms[0].config.enableRewrite == selectStrategy("QF_LIA", f).enableRewrite);
}

TEST_CASE("portfolio: test-arms hook replicates the base arm") {
    setenv("XOLVER_STRAT_PORTFOLIO_TEST_ARMS", "3", 1);
    auto arms = selectPortfolio("QF_NIA", LogicFeatures{});
    unsetenv("XOLVER_STRAT_PORTFOLIO_TEST_ARMS");
    CHECK(arms.size() == 3);
    CHECK(arms[0].label == "base");
    // Replicas are identical to the base — proving idempotence is the point.
    for (size_t i = 1; i < arms.size(); ++i)
        CHECK(arms[i].config.enableRewrite == arms[0].config.enableRewrite);
}

TEST_CASE("portfolio: multi-arm re-entry is idempotent (sat stays sat)") {
    // 3 identical arms via the test hook. The first two arms reach the same
    // sat verdict, so the loop returns on arm 1; either way the answer must be
    // sat and the re-parse between arms must not corrupt state.
    PortfolioEnv guard(3);
    CHECK(static_cast<int>(solveFile(
        "(set-logic QF_LIA)(declare-const x Int)(assert (> x 5))(check-sat)\n", "sat"))
        == static_cast<int>(Result::Sat));
}

TEST_CASE("portfolio: multi-arm re-entry is idempotent (unsat stays unsat)") {
    PortfolioEnv guard(3);
    CHECK(static_cast<int>(solveFile(
        "(set-logic QF_LIA)(declare-const x Int)"
        "(assert (and (> x 5) (< x 2)))(check-sat)\n", "unsat"))
        == static_cast<int>(Result::Unsat));
}

TEST_CASE("portfolio: single base arm is behavior-neutral") {
    // XOLVER_STRAT_PORTFOLIO on, no test-arms hook -> exactly one arm; the
    // verdict must match the plain solve.
    PortfolioEnv guard(1);
    CHECK(static_cast<int>(solveFile(
        "(set-logic QF_LIA)(declare-const x Int)(declare-const y Int)"
        "(assert (= (+ x y) 4))(assert (= x 1))(check-sat)\n", "neutral"))
        == static_cast<int>(Result::Sat));
}

TEST_CASE("portfolio: generous per-arm budget returns the correct verdict") {
    // A large budget spawns+joins the watchdog thread but the solve finishes
    // well before the deadline, so the verdict is exact -- this exercises the
    // full threaded path (spawn -> done -> join) without an interrupt firing.
    BudgetEnv guard(60000);
    CHECK(static_cast<int>(solveFile(
        "(set-logic QF_LIA)(declare-const x Int)(assert (> x 5))(check-sat)\n", "bsat"))
        == static_cast<int>(Result::Sat));
    CHECK(static_cast<int>(solveFile(
        "(set-logic QF_LIA)(declare-const x Int)"
        "(assert (and (> x 5) (< x 2)))(check-sat)\n", "bunsat"))
        == static_cast<int>(Result::Unsat));
}

TEST_CASE("portfolio: per-arm budget is sound (timeout -> unknown, never wrong)") {
    // A 1ms budget may or may not interrupt the solve; either way the result
    // must be the correct verdict OR unknown -- a budget can only relax a
    // verdict to unknown, never flip it.
    BudgetEnv guard(1);
    Result rs = solveFile(
        "(set-logic QF_LIA)(declare-const x Int)(assert (> x 5))(check-sat)\n", "tsat");
    CHECK((rs == Result::Sat || rs == Result::Unknown));
    Result ru = solveFile(
        "(set-logic QF_LIA)(declare-const x Int)"
        "(assert (and (> x 5) (< x 2)))(check-sat)\n", "tunsat");
    CHECK((ru == Result::Unsat || ru == Result::Unknown));
}
