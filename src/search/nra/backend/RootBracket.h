#pragma once

#include "base/WorkBudget.h"
#include <gmpxx.h>
#include <functional>
#include <optional>
#include <utility>
#include <vector>

namespace xolver::nra_backend {

struct RootBracket { mpq_class lower, upper; };

// Compare a rational point with one fixed real root: negative, zero, positive,
// or nullopt when the comparison cannot be certified.
using RationalRootComparison = std::function<std::optional<int>(const mpq_class&)>;

// The input brackets contain two certified roots, in strictly increasing
// order. Construct nested, strictly disjoint brackets for those same roots.
// Exact comparisons justify every endpoint change, including point roots.
// The caller owns work and deadline policy; there is no precision cutoff.
std::optional<std::pair<RootBracket, RootBracket>> separateRootBrackets(
    RootBracket left, RootBracket right,
    const RationalRootComparison& compareLeft,
    const RationalRootComparison& compareRight, WorkBudget& work);

// Input non-root endpoints isolate exactly one real root of the high-to-low
// integer polynomial; an already isolated point root is also accepted.
// Return a dyadic subinterval isolating that same root, or a
// verified rational root as a point. Evaluation intermediates must fit the
// supplied bit budget. Failure preserves the caller's unresolved obligation.
std::optional<RootBracket> compactRootBracket(
    const std::vector<mpz_class>& coefficients, const mpq_class& lower,
    const mpq_class& upper, std::size_t bitBudget, WorkBudget& work);

} // namespace xolver::nra_backend
