#include "search/refute/PolynomialLinearRefutation.h"
#include "search/lra/GeneralSimplex.h"
#include "base/WorkBudget.h"
#include <algorithm>
#include <map>

namespace xolver {

std::optional<std::vector<SatLit>> refutePolynomialLinearRelaxation(
    const std::vector<SignRefuteConstraint>& constraints,
    std::chrono::steady_clock::time_point deadline,
    PolynomialLinearStatistics* statistics) {
    PolynomialLinearStatistics local;
    auto& stats = statistics ? *statistics : local;
    stats = {};
    try {
        WorkBudget work(100000);
        auto tick = [&](size_t amount = 1) {
            work.tick(amount);
            if (std::chrono::steady_clock::now() >= deadline)
                throw ResourceExhausted("polynomial linear relaxation allocation exhausted");
        };
        tick();
        GeneralSimplex simplex;
        std::map<MonomialKey, int> variables;
        for (const auto& constraint : constraints) {
            tick();
            if (constraint.rel == Relation::Neq) continue;
            for (const auto& [monomial, coefficient] : constraint.poly.terms()) {
                tick(1 + monomial.size() + mpz_sizeinbase(coefficient.get_num_mpz_t(), 2) +
                     mpz_sizeinbase(coefficient.get_den_mpz_t(), 2));
            }
            mpq_class constant = 0;
            std::vector<std::pair<int, mpq_class>> terms;
            for (const auto& [monomial, coefficient] : constraint.poly.terms()) {
                tick();
                if (monomial.empty()) { constant += coefficient; continue; }
                // Canonical monomials share one unconstrained real column
                // across all rows. Every polynomial model induces such a
                // linear model; the converse is deliberately not assumed.
                auto it = variables.find(monomial);
                if (it == variables.end()) {
                    it = variables.emplace(monomial,
                        simplex.addVar("m" + std::to_string(variables.size()))).first;
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
