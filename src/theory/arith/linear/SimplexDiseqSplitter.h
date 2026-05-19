#pragma once

#include "theory/core/TheorySolver.h"
#include "theory/core/TheoryLemmaDatabase.h"
#include "theory/arith/lra/GeneralSimplex.h"
#include <vector>

namespace nlcolver {

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
template <typename DiseqInfoT, typename SplitBuilder>
TheoryCheckResult handleSimplexDisequalities(
    const std::vector<DiseqInfoT>& disequalities,
    const GeneralSimplex& gs,
    TheoryLemmaStorage& lemmaDb,
    SplitBuilder&& buildSplit)
{
    for (const auto& d : disequalities) {
        auto val = gs.value(d.auxVar);
        if (!val.isZero()) continue;

        auto result = buildSplit(d);
        if (result.kind == TheoryCheckResult::Kind::Consistent) continue;
        if (result.kind == TheoryCheckResult::Kind::Lemma && result.lemmaOpt) {
            if (lemmaDb.contains(*result.lemmaOpt)) {
                return TheoryCheckResult::unknown();
            }
            lemmaDb.insertIfNew(*result.lemmaOpt);
        }
        return result;
    }
    return TheoryCheckResult::consistent();
}

} // namespace nlcolver
