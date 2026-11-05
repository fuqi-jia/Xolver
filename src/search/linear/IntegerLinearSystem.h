#pragma once

#include <gmpxx.h>

#include <cstddef>
#include <optional>
#include <utility>
#include <vector>

namespace xolver {

struct IntegerLinearEquation {
    // Column indices may be unsorted or repeated; coefficients are added.
    std::vector<std::pair<size_t, mpz_class>> coefficients;
    mpz_class rhs;
};

struct IntegerLinearSystemSolution {
    bool consistent = true;
    size_t rank = 0;
    std::vector<mpz_class> particular;
    // The projection on coordinate i is particular[i] + coordinatePeriods[i]*Z.
    // Zero denotes a fixed value. These projections do not describe correlations
    // between coordinates and must not alone establish a joint model.
    std::vector<mpz_class> coordinatePeriods;
    // Present exactly when the full solution lattice has one free dimension.
    std::optional<std::vector<mpz_class>> lineDirection;
    // An inconsistent subsystem, indexed by rows of the original matrix.
    std::vector<size_t> conflictRows;
};

// Analyze sparse A*x=b over integers. Independent variable components are factored
// separately; no dense transform spanning unrelated components is constructed.
// Every coefficient's column index must be smaller than columns.
IntegerLinearSystemSolution solveIntegerLinearSystem(
    size_t columns, const std::vector<IntegerLinearEquation>& equations);

} // namespace xolver
