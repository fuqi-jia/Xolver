#pragma once

#include "search/linearizer/LinearizationTypes.h"
#include <vector>
#include <optional>

namespace xolver {

class SquareCutGenerator {
public:
    std::vector<LinearCut> generate(
        const AuxTerm& s,
        const std::string& x,
        const LinearizationBounds& xBounds,
        SatLit nonlinearReason,
        const std::optional<mpq_class>& modelX, // for tangent point
        // Sort of the linearized constraint vars. Int by default (NIA legacy);
        // the NRA cut-feeder passes Real so the LRA sibling reads real atoms.
        SortKind sort = SortKind::Int);
};

} // namespace xolver
