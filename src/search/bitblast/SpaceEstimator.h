#pragma once

#include "algebra/poly/PolynomialKernel.h"
#include "search/nia/preprocess/NiaNormalizer.h"
#include "search/nia/core/DomainStore.h"
#include <gmpxx.h>
#include <string>
#include <unordered_map>
#include <vector>

namespace xolver::bitblast {

struct BitWidthPlan {
    std::unordered_map<std::string, unsigned> width;
    bool boxIsComplete = false;
};

// Exact widths for hard-bounded variables and the two-bit starting width for
// unbounded search. Include domain-only variables; boxIsComplete is true only
// when every encoded variable has both bounds. Search owns width refinement.
class SpaceEstimator {
public:
    explicit SpaceEstimator(PolynomialKernel& kernel) : kernel_(kernel) {}

    BitWidthPlan estimate(const std::vector<NormalizedNiaConstraint>& cs,
                          const DomainStore& domains) const;

    // Smallest two's-complement width w with -2^(w-1) <= lo and hi <= 2^(w-1)-1.
    static unsigned bitsToCover(const mpz_class& lo, const mpz_class& hi);

private:
    PolynomialKernel& kernel_;

};

} // namespace xolver::bitblast
