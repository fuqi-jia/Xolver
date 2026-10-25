#pragma once

#include "search/linear/IntegerReasoner.h"

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

} // namespace xolver
