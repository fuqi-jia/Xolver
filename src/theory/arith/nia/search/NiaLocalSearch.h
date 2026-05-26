#pragma once

#include "theory/arith/nia/preprocess/NiaNormalizer.h"
#include "theory/arith/nia/search/IntegerModelValidator.h"
#include "theory/arith/nia/core/DomainStore.h"
#include <cstdint>
#include <optional>

namespace zolver {

/**
 * NiaLocalSearch: heuristic SAT finder for NIA.
 *
 * tryFindModel runs a deterministic seed-and-hill-climb pass; with
 * ZOLVER_NIA_LOCALSEARCH set it additionally runs a focused stochastic
 * local search (tryFindModelSls). All returned models are candidates —
 * NiaSolver validates them via IntegerModelValidator before reporting SAT,
 * so this finder can never make the solver unsound.
 */
class NiaLocalSearch {
public:
    explicit NiaLocalSearch(PolynomialKernel& kernel);

    std::optional<IntegerModel> tryFindModel(
        const std::vector<NormalizedNiaConstraint>& constraints,
        const DomainStore& domains);

    // Focused WalkSAT-style stochastic local search: random restarts + noisy
    // focused moves on a violated constraint, scored by `violation`. Returns a
    // model only when it exactly satisfies every constraint (violation == 0).
    // Seeded for reproducibility. Always runs, independent of the env flag.
    static constexpr uint64_t kDefaultSlsSeed = 0x9E3779B97F4A7C15ull;
    std::optional<IntegerModel> tryFindModelSls(
        const std::vector<NormalizedNiaConstraint>& constraints,
        const DomainStore& domains,
        uint64_t seed = kDefaultSlsSeed);

    // True iff ZOLVER_NIA_LOCALSEARCH is set. NiaSolver gates the (more
    // expensive) SLS pass on this + full effort so it does not run per-check.
    bool slsEnabled() const { return slsEnabled_; }

private:
    PolynomialKernel& kernel_;
    bool slsEnabled_;

    mpz_class violation(const IntegerModel& model,
                        const std::vector<NormalizedNiaConstraint>& constraints) const;

    // Exact satisfaction check (correct relation semantics). A model is only
    // ever returned when this holds, so a returned model is always a genuine
    // model regardless of the heuristic scorer's quirks.
    bool satisfies(const IntegerModel& model,
                   const std::vector<NormalizedNiaConstraint>& constraints) const;
};

} // namespace zolver
