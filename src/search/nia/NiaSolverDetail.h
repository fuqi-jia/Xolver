#pragma once
#include <string>
#include <unordered_set>
#include <vector>
#include "search/nia/preprocess/NiaNormalizer.h"  // NormalizedNiaConstraint
#include "algebra/poly/PolynomialKernel.h"          // PolynomialKernel

namespace xolver {

// Union of variable names appearing across a set of normalized NIA constraints.
inline std::unordered_set<std::string> collectVars(
    const std::vector<NormalizedNiaConstraint>& constraints,
    PolynomialKernel& kernel) {
    std::unordered_set<std::string> vars;
    for (const auto& c : constraints) {
        for (const auto& v : kernel.variables(c.poly)) {
            vars.insert(v);
        }
    }
    return vars;
}

}  // namespace xolver
