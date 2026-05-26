#pragma once

#include "theory/core/LogicFeatureDetector.h"
#include <string>
#include <utility>
#include <vector>

namespace zolver {

/**
 * StrategyPresets (ZOLVER_STRAT_PRESETS) — per-logic strategy selection.
 *
 * The campaign backbone: a single place that maps (declared logic + cheap
 * LogicFeatureDetector features) to a set of solver knobs. Each theory agent's
 * default-OFF technique flag plugs in here, so one static binary can run a
 * tuned configuration per instance class.
 *
 * Soundness: a preset only flips knobs that are *individually* sound (each is a
 * default-OFF, separately-validated flag). It NEVER changes a verdict on its
 * own. The whole mechanism is gated behind ZOLVER_STRAT_PRESETS (default OFF),
 * and any explicit user option / env var overrides the preset (so per-flag A/B
 * testing keeps working).
 *
 * Phase 1 scope: only knobs that EXIST and are validated in this branch are
 * actually enabled (the formula rewriter; the LIA tuning flags are surfaced but
 * left at their defaults pending benchmark data). Cross-agent env flags are
 * carried in `envFlags` for the master to populate once those branches merge —
 * see the documented recommended table in StrategyPresets.cpp.
 */
struct StrategyConfig {
    // In-process knobs (owned/reachable by Solver.cpp in this branch).
    bool enableRewrite = false;        // ZOLVER_PP_REWRITE equivalent

    // LIA tuning flags (mirror the lia-* solver options). Default = current
    // engine defaults, i.e. behavior-neutral until tuned in Phase 2.
    bool liaSafeMode = false;
    bool liaUltraSafeMode = false;
    bool liaEnableSingleVar = false;
    bool liaEnableGcdIneq = false;
    bool liaEnableEqGcdNorm = false;

    // Cross-agent env flags this strategy recommends, as (NAME, "1") pairs.
    // Applied with setenv(NAME, value, /*overwrite=*/0) so an explicit user env
    // ALWAYS wins. Empty in Phase 1 (cross-agent flags live on unmerged
    // branches and cannot be validated here yet).
    std::vector<std::pair<std::string, std::string>> envFlags;
};

// Pick a strategy for (logic, features). Pure: no side effects.
StrategyConfig selectStrategy(const std::string& logic, const LogicFeatures& features);

/**
 * Portfolio (ZOLVER_STRAT_PORTFOLIO) — an ORDERED list of strategy arms tried
 * until one returns a definitive (Sat/Unsat) verdict.
 *
 * This is the assembly seam for the campaign: as each cross-agent technique
 * flag passes its double gate, the master adds a differentiated arm here (e.g.
 * "NIA: bit-blast first, then local-search"). The executor (Solver) runs the
 * arms in order from PRISTINE state (full reset + re-parse per arm), so trying
 * several configurations is sound — any arm's Sat/Unsat is already
 * ModelValidator-backed (invariant 1), and arms can only differ in COMPLETENESS,
 * never in soundness. The FIRST definitive answer wins; an arm that returns
 * Unknown falls through to the next.
 *
 * Phase 1: a single "base" arm (== selectStrategy), so a portfolio run is
 * behavior-neutral until the master populates more arms.
 */
struct PortfolioArm {
    StrategyConfig config;
    std::string label;       // human-readable, for tracing/telemetry
    int budgetMs = 0;        // per-arm soft time budget (0 = no limit). Seam for
                             // the anytime executor; not yet enforced in Phase 1.
};

// Build the ordered portfolio for (logic, features). Always returns >= 1 arm;
// arm[0] is the base strategy. Pure except for an explicit test hook:
// ZOLVER_STRAT_PORTFOLIO_TEST_ARMS=N (N>=1) replicates the base arm N times so
// the multi-arm executor path can be exercised without a promoted flag yet.
std::vector<PortfolioArm> selectPortfolio(const std::string& logic,
                                          const LogicFeatures& features);

} // namespace zolver
