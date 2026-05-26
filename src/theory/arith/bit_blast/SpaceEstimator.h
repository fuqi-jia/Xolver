#pragma once

#include "theory/arith/poly/PolynomialKernel.h"
#include "theory/arith/nia/preprocess/NiaNormalizer.h"
#include "theory/arith/nia/core/DomainStore.h"
#include <gmpxx.h>
#include <string>
#include <unordered_map>
#include <vector>

namespace zolver::bitblast {

struct BitWidthPlan {
    std::unordered_map<std::string, unsigned> width;
    bool boxIsComplete = false;
};

// Part 1 ("where solutions can be"): per-variable bit-width sizing.
// Variable set = vars(cs) ∪ {vars carrying any DomainStore restriction}, so
// domain-only variables are still encoded/validated downstream.
//
// Hard-bounded vars get a width that exactly covers [lb,ub] (so width-growing
// arithmetic is overflow-free). UNBOUNDED vars get a heuristic width = the max of
// four BLAN-style signals:
//   - Multiplication-Adaptation (MA): a base width that shrinks as the number of
//     multiplications grows.
//   - Coefficient-Matching (CM): bits for the largest |coefficient| seen with the
//     var, clipped to K.
//   - Distinct-Graph (DG): if the var must differ from `d` others (edges in the
//     graph of binary `xi != xj` constraints), its closed distinct-set has d+1
//     members, so it needs at least ceil(log2(d+1)) bits to take that many
//     distinct values. (E.g. distinct(x1..x7): d=6 -> ceil(log2 7) = 3 bits.)
// Then a Vote pass (VO): if one width covers > Gamma of the unbounded vars, unify
// them all to it (largest among ties) — a uniform guess that often solves directly.
//
// Vote and the heuristic signals NEVER touch hard-bounded vars: their width stays
// the exact bitsToCover([lb,ub]) so complete-mode soundness is preserved.
// boxIsComplete iff EVERY var in the set is hard-bounded.
class SpaceEstimator {
public:
    explicit SpaceEstimator(PolynomialKernel& kernel) : kernel_(kernel) {}

    BitWidthPlan estimate(const std::vector<NormalizedNiaConstraint>& cs,
                          const DomainStore& domains) const;

    // Smallest two's-complement width w with -2^(w-1) <= lo and hi <= 2^(w-1)-1.
    static unsigned bitsToCover(const mpz_class& lo, const mpz_class& hi);

    // Smallest width w >= 1 with 2^w >= n (i.e. ceil(log2 n) for n >= 2, else 1).
    // A signed w-bit var holds 2^w distinct values, so this is the width needed to
    // hold n distinct values (DG) or to represent magnitude n (CM). BLAN blastBitLength.
    static unsigned bitsToHold(const mpz_class& n);

    // Heuristic refinement: DOUBLE every width (capped at maxBW). Doubling lets
    // the loop reach large widths in a few iterations; an additive step with a
    // low iteration cap would leave a high maxBW unreachable.
    static BitWidthPlan grow(BitWidthPlan plan, unsigned maxBW);

private:
    PolynomialKernel& kernel_;

    static constexpr unsigned kCoeffClipBits = 16;  // CM clip (BLAN K)
    static constexpr double   kVoteThreshold = 0.5; // VO threshold (BLAN Gamma)
};

} // namespace zolver::bitblast
