#pragma once

#include "theory/arith/poly/PolynomialKernel.h"
#include "theory/arith/nia/preprocess/NiaNormalizer.h"
#include "theory/arith/nia/core/DomainStore.h"
#include <gmpxx.h>
#include <string>
#include <unordered_map>
#include <vector>

namespace nlcolver::bitblast {

struct BitWidthPlan {
    std::unordered_map<std::string, unsigned> width;
    bool boxIsComplete = false;
};

// Part 1 ("where solutions can be"): per-variable bit-width sizing.
// Variable set = vars(cs) ∪ {vars carrying any DomainStore restriction}, so
// domain-only variables are still encoded/validated downstream. Hard-bounded
// vars get a width that exactly covers [lb,ub] (so width-growing arithmetic is
// overflow-free); unbounded vars get a heuristic width from coefficient
// magnitude (BLAN Coefficient-Matching) and multiplication count (BLAN
// Multiplication-Adaptation). boxIsComplete iff EVERY var in that set is
// hard-bounded.
class SpaceEstimator {
public:
    explicit SpaceEstimator(PolynomialKernel& kernel) : kernel_(kernel) {}

    BitWidthPlan estimate(const std::vector<NormalizedNiaConstraint>& cs,
                          const DomainStore& domains) const;

    // Smallest two's-complement width w with -2^(w-1) <= lo and hi <= 2^(w-1)-1.
    static unsigned bitsToCover(const mpz_class& lo, const mpz_class& hi);

    // Heuristic refinement: DOUBLE every width (capped at maxBW). Doubling lets
    // the loop reach large widths in a few iterations; an additive step with a
    // low iteration cap would leave a high maxBW unreachable.
    static BitWidthPlan grow(BitWidthPlan plan, unsigned maxBW);

private:
    PolynomialKernel& kernel_;
};

} // namespace nlcolver::bitblast
