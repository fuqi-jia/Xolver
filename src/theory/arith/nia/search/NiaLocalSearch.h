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

    // Enable the WalkSAT / accelerated-hill-climb search (XOLVER_NIA_LOCALSEARCH,
    // default-OFF). Settable for tests.
    void setEnhanced(bool e) { enhanced_ = e; }
    // Phase L1: enable the LS-IA + Yices2LS-style enhancements on top of the
    // base walkSat — incremental per-clause violation tracking, PAWS clause
    // weights, accelerated hill-climb with adaptive step (acc=1.2).
    // Default-OFF (XOLVER_NIA_LS_TWO_LEVEL=1). Pure perf / SAT-finder
    // improvement; soundness invariants unchanged (candidate-only,
    // validator-gated, never returns UNSAT).
    void setTwoLevel(bool e) { twoLevel_ = e; }

private:
    PolynomialKernel& kernel_;
    long budgetMs_;
    long totalBudgetMs_;
    long cumulativeMs_ = 0;
    bool enhanced_ = false;
    bool twoLevel_ = false;

    mpz_class violation(const IntegerModel& model,
                        const std::vector<NormalizedNiaConstraint>& constraints) const;

    // WalkSAT with discrete-Newton critical moves: pick a violated constraint,
    // jump a variable toward the value that satisfies it (Yices2-style
    // accelerated hill-climbing + feasible-set jumping), with random noise and
    // restarts to escape local minima. Returns a satisfying assignment or
    // nullopt; the result is a candidate only (the caller validates it), so the
    // search is always sound regardless of heuristic choices.
    std::optional<IntegerModel> walkSat(
        const std::vector<NormalizedNiaConstraint>& constraints,
        const std::vector<std::string>& vars,
        const DomainStore& domains);

    // Phase L1: enhanced WalkSAT with incremental clause-violation tracking
    // (O(affected) per move instead of O(n) full re-evaluation), PAWS
    // clause weights (hard clauses accumulate weight on plateau), and
    // accelerated hill-climb with adaptive step size (acc=1.2 successive:
    // step, step*acc, step*acc^2). Falls back semantically to walkSat
    // (same Sat-finder contract — candidate only, validator-gated).
    std::optional<IntegerModel> walkSatTwoLevel(
        const std::vector<NormalizedNiaConstraint>& constraints,
        const std::vector<std::string>& vars,
        const DomainStore& domains);
};

} // namespace xolver
