#pragma once
#include "quantifiers/real/Problem.h"
#include <optional>
namespace xolver::quantifiers::real {
// Existential coefficients followed by universal real variables. A conjunction
// of polynomial identities reduces to its coefficient equations; this backend
// solves those equations when they are linear in the existential coefficients.
std::optional<SolverAnswer> solveIdentities(const Problem &, Resources &);
} // namespace xolver::quantifiers::real
