#pragma once

#include "algebra/poly/PolynomialKernel.h"
#include <algorithm>
#include <map>
#include <optional>

namespace xolver {

struct CommonMonomialFactor {
    std::map<VarId, int> powers;
    std::vector<PolynomialKernel::MonomialTerm> quotient;
};

// Exact p = m*q decomposition of canonical integer monomial terms. Constants
// and unsupported powers leave the original representation untouched.
inline std::optional<CommonMonomialFactor> factorCommonMonomial(
    const std::vector<PolynomialKernel::MonomialTerm>& terms) {
    CommonMonomialFactor result;
    result.quotient = terms;
    std::erase_if(result.quotient, [](const auto& term) { return term.coefficient == 0; });
    if (result.quotient.empty()) return std::nullopt;
    for (const auto& term : result.quotient)
        for (const auto& [variable, exponent] : term.powers) {
            (void)variable;
            if (exponent <= 0) return std::nullopt;
        }
    result.powers.insert(result.quotient.front().powers.begin(), result.quotient.front().powers.end());
    for (size_t i = 1; i < result.quotient.size() && !result.powers.empty(); ++i) {
        for (auto it = result.powers.begin(); it != result.powers.end();) {
            const auto& powers = result.quotient[i].powers;
            const auto found = std::find_if(powers.begin(), powers.end(),
                [&](const auto& power) { return power.first == it->first; });
            if (found == powers.end()) it = result.powers.erase(it);
            else { it->second = std::min(it->second, found->second); ++it; }
        }
    }
    if (result.powers.empty()) return std::nullopt;
    for (auto& term : result.quotient) {
        for (auto& [variable, exponent] : term.powers)
            if (const auto found = result.powers.find(variable); found != result.powers.end())
                exponent -= found->second;
        std::erase_if(term.powers, [](const auto& power) { return power.second == 0; });
    }
    return result;
}

} // namespace xolver
