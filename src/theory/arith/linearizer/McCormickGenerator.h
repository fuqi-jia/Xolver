#pragma once

#include "theory/arith/linearizer/LinearizationTypes.h"
#include <vector>

namespace xolver {

class McCormickGenerator {
public:
    // Returns empty if any bound missing or incomplete.
    std::vector<LinearCut> generate(
        const AuxTerm& t,
        const std::string& x, const std::string& y,
        const BoundInfo& xBounds,
        const BoundInfo& yBounds,
        SatLit nonlinearReason,
        // Sort of the linearized constraint vars. Int by default (NIA legacy);
        // the NRA cut-feeder passes Real so the LRA sibling reads real atoms.
        SortKind sort = SortKind::Int);
};

} // namespace xolver
