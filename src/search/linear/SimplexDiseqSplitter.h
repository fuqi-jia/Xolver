#pragma once

#include "contracts/TheorySolver.h"
#include "search/coordination/TheoryLemmaDatabase.h"
#include "search/lra/GeneralSimplex.h"
#include <utility>
#include <vector>

namespace xolver {

// ============================================================================
// Unified disequality handler for simplex-based solvers (LRA, LIA).
//
// Usage:
//   return handleSimplexDisequalities(
//       disequalities_, gs_, lemmaDb,
//       [this](const DiseqInfo& d) -> TheoryCheckResult {
//           // theory-specific split logic
//       });
//
// The DiseqInfoT type must provide:
//   - int auxVar
//   - SatLit lit
// ============================================================================
template <typename DiseqInfoT, typename SplitBuilder, typename ModelViolation>
TheoryCheckResult handleSimplexDisequalities(
    const std::vector<DiseqInfoT>& disequalities,
    const GeneralSimplex& gs,
    TheoryLemmaStorage& lemmaDb,
    SplitBuilder&& buildSplit,
    ModelViolation&& violatesModel)
{
    for (const auto& d : disequalities) {
        auto val = gs.value(d.auxVar);
        if (!violatesModel(d, val)) continue;

        auto result = buildSplit(d);
        if (result.kind == TheoryCheckResult::Kind::Consistent) continue;
        if (result.kind == TheoryCheckResult::Kind::Lemma && result.lemmaOpt) {
            if (lemmaDb.isInstalled(*result.lemmaOpt)) {
                return TheoryCheckResult::unknown();
            }
        }
        return result;
    }
    return TheoryCheckResult::consistent();
}

// Dense theories only need a split at zero. Discrete theories can supply a
// predicate and let their builder exclude a wider unreachable model interval.
template <typename DiseqInfoT, typename SplitBuilder>
TheoryCheckResult handleSimplexDisequalities(
    const std::vector<DiseqInfoT>& disequalities,
    const GeneralSimplex& gs,
    TheoryLemmaStorage& lemmaDb,
    SplitBuilder&& buildSplit)
{
    return handleSimplexDisequalities(disequalities, gs, lemmaDb,
        std::forward<SplitBuilder>(buildSplit),
        [](const DiseqInfoT&, const DeltaRational& value) { return value.isZero(); });
}

} // namespace xolver
