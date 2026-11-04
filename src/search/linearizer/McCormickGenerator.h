#pragma once

#include "search/linearizer/LinearizationTypes.h"
#include <vector>

namespace xolver {

class McCormickGenerator {
public:
    // Generate each envelope face whose two required endpoints have complete
    // explanations. Opposite bounds may be absent. Open zero endpoints also
    // retain the strict product sign over the reals.
    std::vector<LinearCut> generate(
        const AuxTerm& t,
        const std::string& x, const std::string& y,
        const LinearizationBounds& xBounds,
        const LinearizationBounds& yBounds,
        SatLit nonlinearReason,
        // Integer callers use Int; real callers use Real for the LRA sibling.
        SortKind sort = SortKind::Int);
};

} // namespace xolver
