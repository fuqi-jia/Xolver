#pragma once
#include "search/linear/LinearConstraintRegistration.h"

namespace xolver {
// NIA and NRA share premise handling and atom registration. The integer/real
// distinction is explicit, so strict integer rounding stays in one normalizer.
template<class Assignment>
std::vector<TheoryLemma> mirrorLinearBounds(
    const std::vector<Assignment>& assignments, SortKind sort,
    PolynomialKernel& kernel, TheoryAtomRegistry* registry, TheoryId target) {
    std::vector<TheoryLemma> lemmas;
    if (!registry) return lemmas;
    for (const auto& assignment : assignments) {
        std::optional<ZeroLinearConstraint> constraint;
        if (const auto* linear = std::get_if<LinearAtomPayload>(&assignment.atom.payload))
            constraint = LinearConstraintNormalizer::makeEffectiveConstraint(
                *linear, assignment.value, sort);
        else if (const auto* poly = std::get_if<PolynomialAtomPayload>(&assignment.atom.payload))
            constraint = LinearConstraintNormalizer::makeEffectiveConstraint(
                *poly, assignment.value, sort, kernel);
        if (!constraint) continue;
        const auto lit = registerLinearConstraint(*registry, *constraint, target);
        if (lit.var) lemmas.push_back(TheoryLemma{{assignment.lit.negated(), lit}});
    }
    return lemmas;
}
} // namespace xolver
