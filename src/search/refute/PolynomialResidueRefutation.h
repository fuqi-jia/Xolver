#pragma once

#include "search/refute/SignDefinitenessRefuter.h"
#include <chrono>

namespace xolver {

struct PolynomialResidueLimits {
    std::vector<int> moduli{2, 3, 4, 5, 7, 8, 9, 11};
    size_t variables = 15;
    size_t assignments = 50000;
    size_t work = 100000;
    std::chrono::steady_clock::time_point deadline =
        std::chrono::steady_clock::time_point::max();
};

struct PolynomialResidueStatistics {
    size_t moduli = 0, components = 0, variables = 0;
    size_t assignments = 0, evaluations = 0;
    bool exhausted = false;
};

// All polynomial variables must denote integers. Rational coefficients are
// cleared exactly. Reduce coefficients before finding connected components:
// quotient variables multiplied by the modulus then disappear. A component
// with no residue assignment explains a conflict using its original equality
// premises. Inequalities and disequalities are ignored; an open modular
// relaxation, unsupported modulus or exhausted budget never establishes SAT.
std::optional<std::vector<SatLit>> refuteByPolynomialResidues(
    const std::vector<SignRefuteConstraint>&,
    const PolynomialResidueLimits& = {}, PolynomialResidueStatistics* = nullptr);

} // namespace xolver
