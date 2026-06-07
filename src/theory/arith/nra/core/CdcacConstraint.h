#pragma once

#include "expr/types.h"
#include "sat/SatSolver.h"
#include <vector>
#include <optional>
#include <unordered_set>

namespace xolver {

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
    // cvc5-style integer-aware CAD: variables that must take INTEGER values. When
    // non-empty (and XOLVER_NRA_CAC_INT is on), sample selection for these vars is
    // restricted to integers, so the CAD yields integer models / excludes
    // non-integer cells directly. Empty ⇒ pure-real behaviour (byte-identical).
    std::unordered_set<VarId> integerVars;
};

} // namespace xolver
