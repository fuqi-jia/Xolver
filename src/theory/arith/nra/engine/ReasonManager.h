#pragma once

#include "theory/arith/nra/core/CdcacTypes.h"
#include "theory/core/TheorySolver.h"
#include <vector>

namespace nlcolver {

/**
 * Collects and minimizes conflict reasons from coverings.
 *
 * P0: simple union + dedup.
 * P5: safe deletion-based minimization.
 */
class ReasonManager {
public:
    // Collect all reasons from a covering, deduplicated.
    static std::vector<SatLit> minimize(const Covering& cover);

    // Convert a set of reasons (active true literals) to a TheoryConflict
    // by negating each literal.
    static TheoryConflict toConflict(const std::vector<SatLit>& reasons);

    // Deduplicate a vector of SatLits (stable).
    static std::vector<SatLit> deduplicate(std::vector<SatLit> lits);
};

} // namespace nlcolver
