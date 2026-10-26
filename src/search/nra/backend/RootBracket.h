#pragma once

#include "base/WorkBudget.h"
#include <gmpxx.h>
#include <optional>
#include <vector>

namespace xolver::nra_backend {

struct RootBracket { mpq_class lower, upper; };

// Input non-root endpoints isolate exactly one real root of the high-to-low
// integer polynomial; an already isolated point root is also accepted.
// Return a dyadic subinterval isolating that same root, or a
// verified rational root as a point. Evaluation intermediates must fit the
// supplied bit budget. Failure preserves the caller's unresolved obligation.
std::optional<RootBracket> compactRootBracket(
    const std::vector<mpz_class>& coefficients, const mpq_class& lower,
    const mpq_class& upper, std::size_t bitBudget, WorkBudget& work);

} // namespace xolver::nra_backend
