#pragma once

#include "theory/arith/kernel/linearizer/LinearizationTypes.h"
#include <vector>
#include <optional>

namespace xolver {

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
        bool emitTangent = true,
        // Sort of the linearized constraint vars. Int by default (NIA legacy);
        // the NRA cut-feeder passes Real so the LRA sibling reads real atoms.
        SortKind sort = SortKind::Int);
};

} // namespace xolver
