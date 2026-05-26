#include "frontend/factory/StrategyPresets.h"

#include <cstdlib>

namespace zolver {

// Helper: normalize "QF_X" / "X" comparisons.
static bool isLogic(const std::string& l, std::initializer_list<const char*> names) {
    for (const char* n : names) if (l == n) return true;
    return false;
}

StrategyConfig selectStrategy(const std::string& logic, const LogicFeatures& features) {
    StrategyConfig c;

    // ---------------------------------------------------------------------
    // Phase-1 knob: the formula rewriter (ZOLVER_PP_REWRITE). It is validated
    // behavior-neutral across the whole regression corpus, and its boolean /
    // constant simplifications pay off most on logics with rich boolean
    // structure or many constants. Enable it everywhere we support; the
    // per-logic granularity below is the tuning point for Phase 2.
    // ---------------------------------------------------------------------
    c.enableRewrite = true;

    // ---------------------------------------------------------------------
    // LIA tuning flags. Left at engine defaults (all false) until benchmark
    // data justifies flipping them — surfaced here so the table is the single
    // place to tune them. (features is available for finer keying in Phase 2,
    // e.g. enabling gcd-ineq tightening only when divisibility-like atoms are
    // present.)
    // ---------------------------------------------------------------------
    (void)features;

    // ---------------------------------------------------------------------
    // Cross-agent technique flags (the campaign backbone). These flags live on
    // the per-theory agent branches and are NOT present/validated in this
    // worktree, so Phase 1 leaves `envFlags` empty. Once the master merges a
    // branch and the flag passes its double gate, populate the matching arm
    // below. Applied via setenv(...,overwrite=0): an explicit user env wins.
    //
    // Recommended table (from the bibles' "minimal超越集" + must-do groupings):
    //   QF_NIA / NIA   : ZOLVER_NIA_LOCALSEARCH (WalkSAT SLS),
    //                    ZOLVER_NIA_BITBLAST (bounded bit-blasting)
    //   QF_NRA / NRA   : ZOLVER_NRA_LAZARD_LIFT (Lazard projection; exists here
    //                    but partial — leave to the master), NRA var-order
    //   QF_UF / arrays : ZOLVER_UF_DISEQ_WATCH, ZOLVER_AX_ROW2_CONST,
    //                    ZOLVER_AX_WEAKEQ
    //   combination    : ZOLVER_COMB_CAREGRAPH, ZOLVER_SAT_MIN,
    //                    ZOLVER_SAT_LEMMA_MGMT
    // Example (kept disabled): if (isLogic(logic, {"QF_NIA","NIA"}))
    //                              c.envFlags.push_back({"ZOLVER_NIA_LOCALSEARCH","1"});
    // ---------------------------------------------------------------------

    // Per-logic shape (uniform in Phase 1; explicit arms are the Phase-2 seams).
    if (isLogic(logic, {"QF_LIA", "LIA", "QF_UFLIA", "UFLIA",
                        "QF_ALIA", "ALIA", "QF_AUFLIA", "AUFLIA"})) {
        // LIA family: rewriter on; LIA tuning flags at defaults (see above).
    } else if (isLogic(logic, {"QF_NIA", "NIA", "QF_UFNIA", "UFNIA"})) {
        // NIA family: rewriter on; bit-blast/local-search flags pending merge.
    } else if (isLogic(logic, {"QF_NRA", "NRA", "QF_UFNRA", "UFNRA"})) {
        // NRA family: rewriter on; Lazard/var-order flags pending merge.
    } else if (isLogic(logic, {"QF_UF", "QF_AX"})) {
        // EUF / arrays: rewriter on; EUF/array flags pending merge.
    }
    // Default (LRA/LIRA/NIRA/IDL/RDL/combination/unset): rewriter on.

    return c;
}

std::vector<PortfolioArm> selectPortfolio(const std::string& logic,
                                          const LogicFeatures& features) {
    StrategyConfig base = selectStrategy(logic, features);

    // Phase-1 portfolio is the single base arm. Differentiated arms (e.g. a
    // bit-blast-first arm then a local-search arm for QF_NIA) are appended here
    // by the master as each underlying flag passes its gate; each is just a
    // StrategyConfig with a different envFlags set.
    std::vector<PortfolioArm> arms;
    arms.push_back({base, "base", /*budgetMs=*/0});

    // Test-only hook: replicate the base arm so the multi-arm executor path is
    // exercised by the unit suite without depending on a not-yet-promoted flag.
    // Replicating an IDENTICAL arm must leave the verdict unchanged (proves the
    // per-arm pristine re-entry is sound), so it is safe to gate tests on.
    if (const char* n = std::getenv("ZOLVER_STRAT_PORTFOLIO_TEST_ARMS")) {
        int extra = std::atoi(n) - 1;
        for (int i = 0; i < extra && i < 7; ++i)
            arms.push_back({base, "test-replica", 0});
    }

    return arms;
}

} // namespace zolver
