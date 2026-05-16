#pragma once

#include "theory/arith/nra/CdcacTypes.h"
#include <vector>

namespace nlcolver {

class AlgebraBackend;

/**
 * Manages cells, coverings, and sample selection.
 */
class CoveringManager {
public:
    // Add a cell to a covering.
    static void addCell(Covering& cover, Cell cell);

    // Normalize and merge adjacent compatible cells.
    static void normalizeAndMerge(Covering& cover);

    // Check whether the covering covers the entire real line.
    static CoverageResult coversAllLine(AlgebraBackend* algebra, const Covering& cover);

    // Choose a sample point outside all cells in the covering.
    // If preferred is given and not covered, use it.
    static std::optional<RealAlg> chooseSampleOutside(
        const Covering& cover,
        const std::optional<mpq_class>& preferred);

    // Build a cell containing the given sample from a set of root bounds.
    // Returns Unknown if algebraic comparison is inconclusive.
    static CellLookupResult cellContaining(AlgebraBackend* algebra, VarId var, const RealAlg& sample, const RootSet& roots);
};

} // namespace nlcolver
