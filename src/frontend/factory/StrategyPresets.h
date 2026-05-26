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

} // namespace zolver
