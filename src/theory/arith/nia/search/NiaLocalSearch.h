#pragma once

#include "theory/arith/nia/preprocess/NiaNormalizer.h"
#include "theory/arith/nia/search/IntegerModelValidator.h"
#include "theory/arith/nia/core/DomainStore.h"
#include <optional>

namespace xolver {

/**
 * NiaLocalSearch: heuristic SAT finder for NIA.
 *
 * Phase NIA-Core: skeleton only. Tries a few candidate assignments.
 */
class NiaLocalSearch {
public:
    explicit NiaLocalSearch(PolynomialKernel& kernel);

    std::optional<IntegerModel> tryFindModel(
        const std::vector<NormalizedNiaConstraint>& constraints,
        const DomainStore& domains);

    // Per-call wall-clock budget in ms; <= 0 means unlimited. The search is a
    // heuristic candidate finder, so giving up early just returns nullopt
    // (no model this call) -- always sound. Default from XOLVER_NIA_LS_BUDGET_MS.
    void setBudgetMs(long ms) { budgetMs_ = ms; }

    // Cumulative per-solve budget: the SAT core triggers a full-effort theory
    // check on every complete assignment (hundreds on branchy QF_NIA), each
    // re-running this search from scratch -- futile on UNSAT and ~10s in total.
    // Once cumulative search time exceeds this, the search is skipped entirely
    // (returns nullopt) so the cheap reasoning stages get the time. Sound
    // (candidate-only). Reset per solve. Default from XOLVER_NIA_LS_TOTAL_MS.
    void resetBudget() { cumulativeMs_ = 0; }

private:
    PolynomialKernel& kernel_;
    long budgetMs_;
    long totalBudgetMs_;
    long cumulativeMs_ = 0;

    mpz_class violation(const IntegerModel& model,
                        const std::vector<NormalizedNiaConstraint>& constraints) const;
};

} // namespace xolver
