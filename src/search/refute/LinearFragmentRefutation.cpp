#include "search/refute/LinearFragmentRefutation.h"
#include "search/lra/GeneralSimplex.h"
#include "base/WorkBudget.h"
#include <algorithm>
#include <unordered_map>

namespace xolver {

std::optional<std::vector<SatLit>> refuteLinearFragment(
    const std::vector<SignRefuteConstraint>& constraints,
    std::chrono::steady_clock::time_point deadline,
    LinearFragmentStatistics* statistics) {
    LinearFragmentStatistics local;
    auto& stats = statistics ? *statistics : local;
    stats = {};
    try {
        WorkBudget work(100000);
        auto tick = [&](size_t amount = 1) {
            work.tick(amount);
            if (std::chrono::steady_clock::now() >= deadline)
                throw ResourceExhausted("linear fragment allocation exhausted");
        };
        tick();
        GeneralSimplex simplex;
        std::unordered_map<VarId, int> variables;
        for (const auto& constraint : constraints) {
            tick();
            if (constraint.rel == Relation::Neq) continue;
            bool linear = true;
            for (const auto& [monomial, coefficient] : constraint.poly.terms()) {
                tick(1 + monomial.size() + mpz_sizeinbase(coefficient.get_num_mpz_t(), 2) +
                     mpz_sizeinbase(coefficient.get_den_mpz_t(), 2));
                if (!monomial.empty() && (monomial.size() != 1 || monomial[0].second != 1)) {
                    linear = false;
                    break;
                }
            }
            if (!linear) continue;
            mpq_class constant = 0;
            std::vector<std::pair<int, mpq_class>> terms;
            for (const auto& [monomial, coefficient] : constraint.poly.terms()) {
                tick();
                if (monomial.empty()) { constant += coefficient; continue; }
                const auto variable = monomial[0].first;
                auto it = variables.find(variable);
                if (it == variables.end()) {
                    it = variables.emplace(variable, simplex.addVar("p" + std::to_string(variable))).first;
                    ++stats.variables;
                }
                terms.emplace_back(it->second, coefficient);
            }
            // addConstraint creates s=sum(terms)-rhs. Setting rhs=-constant
            // makes s the original polynomial, including its exact offset.
            const auto row = simplex.addConstraint(terms, -constant);
            if (row < 0) return std::nullopt;
            ++stats.constraints;
            const auto rel = constraint.rel;
            if (rel == Relation::Eq || rel == Relation::Geq || rel == Relation::Gt) {
                const BoundInfo bound(BoundValue(DeltaRational(0, rel == Relation::Gt ? 1 : 0)), constraint.reason);
                simplex.assertLower(row, bound);
            }
            if (rel == Relation::Eq || rel == Relation::Leq || rel == Relation::Lt) {
                const BoundInfo bound(BoundValue(DeltaRational(0, rel == Relation::Lt ? -1 : 0)), constraint.reason);
                simplex.assertUpper(row, bound);
            }
            if (simplex.hasImmediateConflict()) break;
        }
        const auto result = simplex.checkUntil(deadline);
        if (result == GeneralSimplex::Result::Unknown) stats.exhausted = true;
        if (result != GeneralSimplex::Result::Unsat) return std::nullopt;
        std::vector<SatLit> reasons;
        for (const auto& bound : simplex.getConflict())
            if (std::find(reasons.begin(), reasons.end(), bound.reason) == reasons.end())
                reasons.push_back(bound.reason);
        if (!reasons.empty()) return reasons;
    } catch (const ResourceExhausted&) {
        stats.exhausted = true;
    }
    return std::nullopt;
}

} // namespace xolver
