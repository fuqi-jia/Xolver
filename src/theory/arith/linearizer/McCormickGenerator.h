#pragma once

#include "theory/arith/linearizer/LinearizationTypes.h"
#include <vector>

namespace zolver {

class McCormickGenerator {
public:
    // Returns empty if any bound missing or incomplete.
    std::vector<LinearCut> generate(
        const AuxTerm& t,
        const std::string& x, const std::string& y,
        const BoundInfo& xBounds,
        const BoundInfo& yBounds,
        SatLit nonlinearReason);
};

} // namespace zolver
