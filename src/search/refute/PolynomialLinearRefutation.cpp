#include "search/refute/PolynomialLinearRefutation.h"
#include "base/WorkBudget.h"
#include <algorithm>
#include <unordered_set>

namespace xolver {

void PolynomialLinearRefuter::reset() {
    simplex_.reset();
    variables_.clear();
    rows_.clear();
}

std::optional<std::unordered_map<VarId, mpq_class>> PolynomialLinearRefuter::projectCandidate(
    const std::vector<SignRefuteConstraint>& constraints, WorkBudget& work) const {
    try {
        work.tick();
        const auto delta = simplex_.computeSafeDelta();
        std::unordered_map<VarId, mpq_class> point;
        for (const auto& constraint : constraints) {
            work.tick();
            for (const auto& [monomial, coefficient] : constraint.poly.terms()) {
                (void)coefficient;
                for (const auto& [variable, exponent] : monomial) {
                    work.tick();
                    (void)exponent;
                    if (point.contains(variable)) continue;
                    const auto column = variables_.find(MonomialKey{{variable, 1}});
                    if (column == variables_.end()) point.emplace(variable, 0);
                    else {
                        const auto value = simplex_.value(column->second);
                        point.emplace(variable, mpq_class(value.a + value.b * delta));
                    }
                }
            }
        }
        return point;
    } catch (const ResourceExhausted&) {
        return std::nullopt;
    }
}

std::optional<std::vector<SatLit>> PolynomialLinearRefuter::check(
    const std::vector<SignRefuteConstraint>& constraints,
    std::chrono::steady_clock::time_point deadline,
    PolynomialLinearStatistics* statistics) {
    PolynomialLinearStatistics local;
    auto& stats = statistics ? *statistics : local;
    stats = {};
    try {
        WorkBudget work(workLimit_);
        if (wall::hasDeadline())
            deadline = std::min(deadline, std::chrono::steady_clock::now() +
                std::chrono::milliseconds(wall::remainingMs()));
        auto tick = [&](size_t amount = 1) {
            work.tick(amount);
            if (std::chrono::steady_clock::now() >= deadline)
                throw ResourceExhausted("polynomial linear relaxation allocation exhausted");
        };
        tick();
        std::vector<GeneralSimplex::ActiveBound> bounds;
        bounds.reserve(2 * constraints.size());
        std::unordered_set<uint64_t> activeReasons;
        auto reasonKey = [](SatLit literal) {
            return (static_cast<uint64_t>(literal.var) << 1) | literal.sign;
        };
        for (const auto& constraint : constraints) {
            tick();
            if (constraint.rel == Relation::Neq) {
                // Non-convex disequalities are omitted, but the constant
                // contradiction 0 != 0 needs no relaxation or case split.
                if (constraint.poly.isZero()) {
                    ++stats.constraints;
                    return std::vector<SatLit>{constraint.reason};
                }
                continue;
            }
            auto found = rows_.find(constraint.reason.var);
            int row;
            if (found != rows_.end() &&
                found->second.polynomial.terms() == constraint.poly.terms()) {
                row = found->second.variable;
                ++stats.reusedRows;
            } else {
                mpq_class constant = 0;
                std::vector<std::pair<int, mpq_class>> terms;
                for (const auto& [monomial, coefficient] : constraint.poly.terms()) {
                    tick(1 + monomial.size() + mpz_sizeinbase(coefficient.get_num_mpz_t(), 2) +
                         mpz_sizeinbase(coefficient.get_den_mpz_t(), 2));
                    if (coefficient == 0) continue;
                    if (monomial.empty()) { constant += coefficient; continue; }
                    // The columns are independent monomial values. Retained
                    // definitions impose neither product identities nor integrality.
                    auto variable = variables_.find(monomial);
                    if (variable == variables_.end())
                        variable = variables_.emplace(monomial,
                            simplex_.addVar("m" + std::to_string(variables_.size()))).first;
                    terms.emplace_back(variable->second, coefficient);
                }
                row = simplex_.addConstraint(terms, -constant);
                if (row < 0) return std::nullopt;
                rows_.insert_or_assign(constraint.reason.var, Row{constraint.poly, row});
                ++stats.newRows;
            }
            ++stats.constraints;
            activeReasons.insert(reasonKey(constraint.reason));
            const auto rel = constraint.rel;
            if (rel == Relation::Eq || rel == Relation::Geq || rel == Relation::Gt)
                bounds.push_back({row, true, BoundInfo(
                    BoundValue(DeltaRational(0, rel == Relation::Gt ? 1 : 0)), constraint.reason)});
            if (rel == Relation::Eq || rel == Relation::Leq || rel == Relation::Lt)
                bounds.push_back({row, false, BoundInfo(
                    BoundValue(DeltaRational(0, rel == Relation::Lt ? -1 : 0)), constraint.reason)});
        }
        stats.variables = variables_.size();
        stats.retainedRows = simplex_.numRows();
        tick();
        // Replace the complete premise base. An inactive cached row is an
        // unbounded definition, not a surviving assertion or explanation.
        simplex_.replaceActiveBounds(bounds, GeneralSimplex::AssignmentPolicy::Preserve);
        const auto result = simplex_.checkUntil(deadline);
        if (result == GeneralSimplex::Result::Unknown) stats.exhausted = true;
        if (result != GeneralSimplex::Result::Unsat) return std::nullopt;
        std::vector<SatLit> reasons;
        for (const auto& bound : simplex_.getConflict()) {
            if (!activeReasons.count(reasonKey(bound.reason))) return std::nullopt;
            if (std::find(reasons.begin(), reasons.end(), bound.reason) == reasons.end())
                reasons.push_back(bound.reason);
        }
        if (!reasons.empty()) return reasons;
    } catch (const ResourceExhausted&) {
        stats.exhausted = true;
    }
    return std::nullopt;
}

} // namespace xolver
