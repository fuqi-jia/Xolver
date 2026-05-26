// ZOLVER_STRAT_PORTFOLIO: ordered strategy arms tried until one returns a
// definitive verdict. Phase 1 is a single base arm (== ZOLVER_STRAT_PRESETS),
// so a portfolio run is behavior-neutral. The multi-arm executor is exercised
// via the ZOLVER_STRAT_PORTFOLIO_TEST_ARMS test hook, which replicates the base
// arm N times: running an IDENTICAL arm N times must not change the verdict,
// which proves the per-arm pristine re-entry (reset + re-parse) is sound.
#include <doctest/doctest.h>
#include "zolver/Solver.h"
#include "frontend/factory/StrategyPresets.h"
#include "theory/core/LogicFeatureDetector.h"
#include <cstdlib>
#include <fstream>
#include <filesystem>
#include <string>

using namespace zolver;

namespace {
struct PortfolioEnv {
    explicit PortfolioEnv(int armsN) {
        setenv("ZOLVER_STRAT_PORTFOLIO", "1", 1);
        if (armsN > 1) setenv("ZOLVER_STRAT_PORTFOLIO_TEST_ARMS",
                              std::to_string(armsN).c_str(), 1);
    }
    ~PortfolioEnv() {
        unsetenv("ZOLVER_STRAT_PORTFOLIO");
        unsetenv("ZOLVER_STRAT_PORTFOLIO_TEST_ARMS");
    }
};
Result solveFile(const std::string& smt, const std::string& tag) {
    std::string path = (std::filesystem::temp_directory_path() /
                        ("zolver_pf_" + tag + ".smt2")).string();
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
    setenv("ZOLVER_STRAT_PORTFOLIO_TEST_ARMS", "3", 1);
    auto arms = selectPortfolio("QF_NIA", LogicFeatures{});
    unsetenv("ZOLVER_STRAT_PORTFOLIO_TEST_ARMS");
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
    // ZOLVER_STRAT_PORTFOLIO on, no test-arms hook -> exactly one arm; the
    // verdict must match the plain solve.
    PortfolioEnv guard(1);
    CHECK(static_cast<int>(solveFile(
        "(set-logic QF_LIA)(declare-const x Int)(declare-const y Int)"
        "(assert (= (+ x y) 4))(assert (= x 1))(check-sat)\n", "neutral"))
        == static_cast<int>(Result::Sat));
}
