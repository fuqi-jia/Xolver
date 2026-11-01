#pragma once

#include "search/linear/IntegerReasoner.h"
#include "base/WorkBudget.h"

namespace xolver {

using IntegerPoint = std::unordered_map<std::string, mpq_class>;

// Construct an integer candidate on the affine lattice of the equalities.
// Coordinates absent from the equalities retain their seed values. For a
// lattice with at most one free coordinate, all remaining constraints are
// solved exactly as bounds/exclusions on that integer parameter. Otherwise
// no candidate is proposed; callers continue their ordinary search. A failure
// is never an UNSAT result. Constraints must be normalized over integers.
std::optional<IntegerPoint> findIntegerAffineModel(
    const std::vector<NormalizedConstraint>& constraints, const IntegerPoint& seed);

// Repair a relaxation jointly: eliminate unit equalities, move free integer
// coordinates to exact constraint boundaries, then reconstruct dependents.
// Every returned point satisfies all input constraints. Exhaustion or a local
// minimum proposes no model and never proves infeasibility.
std::optional<IntegerPoint> repairIntegerAffineModel(
    const std::vector<NormalizedConstraint>& constraints,
    const IntegerPoint& relaxation, WorkBudget& budget);

} // namespace xolver
