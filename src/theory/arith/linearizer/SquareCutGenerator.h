#pragma once

#include "theory/arith/linearizer/LinearizationTypes.h"
#include <vector>
#include <optional>

namespace nlcolver {

class SquareCutGenerator {
public:
    std::vector<LinearCut> generate(
        const AuxTerm& s,
        const std::string& x,
        const BoundInfo& xBounds,
        SatLit nonlinearReason,
        const std::optional<mpq_class>& modelX, // for tangent point
        bool emitNonneg = true,
        bool emitSecant = true,
        bool emitTangent = true);
};

} // namespace nlcolver
