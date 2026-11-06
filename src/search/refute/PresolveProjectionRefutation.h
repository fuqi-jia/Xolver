#pragma once

#include "contracts/PolynomialDomain.h"
#include "contracts/SatSolver.h"
#include <optional>
#include <vector>

namespace xolver {
class PresolveProjection;
class PolynomialKernel;
class PolynomialLinearRefuter;

// Exact refutation of the reduced obligation. Returned reasons cover the
// original premises actually used, including the equalities used for elimination.
std::optional<std::vector<SatLit>> refutePresolveProjection(
    const PresolveProjection& projection, PolynomialKernel& kernel,
    PolynomialLinearRefuter& linear, PolynomialDomain domain);
} // namespace xolver
