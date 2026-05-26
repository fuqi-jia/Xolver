#pragma once

#include "expr/types.h"
#include "sat/SatSolver.h"
#include <vector>
#include <optional>

namespace zolver {

/**
 * Public constraint type shared between CdcacSolver (facade) and CdcacCore.
 * CdcacCore does NOT depend on CdcacSolver's private ActiveConstraint.
 */
struct CdcacConstraint {
    ConstraintId id = NullConstraintId;
    PolyId poly = NullPoly;
    Relation rel = Relation::Eq;
    SatLit reason{0, true};  // active true literal currently assigned true
    int level = 0;
};

struct CdcacInput {
    std::vector<CdcacConstraint> constraints;
    std::vector<VarId> varOrder;
    std::optional<ModelSeed> seed;
};

} // namespace zolver
