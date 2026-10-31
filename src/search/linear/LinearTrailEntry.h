#pragma once

#include "contracts/SatSolver.h"

namespace xolver {

// The manager owns the immutable (lhs, rhs) behind auxVar. A trail entry only
// records its assertion source and backtrackable interpretation. Keep sourceVar
// separate from lit.var: standalone callers may supply a different reason.
struct LinearTrailEntry {
    int level;
    SatLit lit;
    SatVar sourceVar;
    ExprId expression;
    Relation relation;
    bool value;
    int auxVar;
    bool isDiseq;
    bool integerForm;
};

struct LinearTrailKey {
    SatVar operator()(const LinearTrailEntry& entry) const { return entry.sourceVar; }
};

} // namespace xolver
