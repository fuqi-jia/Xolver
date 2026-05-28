#pragma once
#include "sat/SatSolver.h"
#include <vector>

namespace xolver {

// ---------------------------------------------------------------------------
// Theory-agnostic, always-sound clause minimization for the combination layer
// (XOLVER_SAT_MIN). Generalizes NRA's ReasonMinimizer::minimizeL0 (which was
// CDCAC-Covering-specific) to a theory-independent home so interface / EUF /
// array / arith conflicts and lemmas can all be shortened.
//
// The only reduction applied here is literal DEDUP: a clause containing the
// same literal twice is logically identical to the deduped clause, so removing
// duplicates strictly shortens the learned clause without changing entailment
// (and without affecting whether a conflict is falsified by the current model).
// Shorter learned clauses propagate more and waste less SAT work.
//
// NOT done here (would be unsound without a per-theory entailment oracle):
//   - dropping non-duplicate literals (greedy / set-cover reduction). That
//     requires the theory's validity check (cf. ReasonMinimizer::minimizeL1)
//     and must keep the clause entailed.
//   - removing complementary literals x / ¬x (changes the clause's meaning).
// ---------------------------------------------------------------------------
struct ConflictMinimizer {
    // Remove duplicate literals in place (deterministic order by var, then sign).
    static void dedup(std::vector<SatLit>& lits);

    static std::vector<SatLit> deduped(std::vector<SatLit> lits) {
        dedup(lits);
        return lits;
    }
};

} // namespace xolver
