#include "search/refute/PolynomialLinearRefutation.h"
#include "base/WorkBudget.h"
#include <algorithm>
#include <limits>
#include <set>
#include <unordered_set>

namespace xolver {

void PolynomialLinearRefuter::reset() {
    simplex_.reset();
    variables_.clear();
    rows_.clear();
    productRows_.clear();
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
        WorkBudget construction;
        if (wall::hasDeadline())
            deadline = std::min(deadline, std::chrono::steady_clock::now() +
                std::chrono::milliseconds(wall::remainingMs()));
        auto tick = [&](size_t amount = 1) {
            work.tick(amount);
            if (std::chrono::steady_clock::now() >= deadline)
                throw ResourceExhausted("polynomial linear relaxation allocation exhausted");
        };
        auto build = [&](size_t amount = 1) { tick(amount); construction.tick(amount); };
        tick();
        struct Explanation { int variable; std::vector<SatLit> sources; };
        std::vector<Explanation> explanations;
        auto label = [&](int variable, std::vector<SatLit> sources) {
            build();
            if (explanations.size() >= std::numeric_limits<SatVar>::max() - 1)
                throw ResourceExhausted("polynomial relaxation explanation allocation exhausted");
            explanations.push_back({variable, std::move(sources)});
            return SatLit::positive(static_cast<SatVar>(explanations.size()));
        };
        auto include = [&](std::vector<SatLit>& target, const std::vector<SatLit>& sources) {
            for (auto source : sources) {
                build();
                if (std::find(target.begin(), target.end(), source) == target.end()) target.push_back(source);
            }
        };
        auto expand = [&](const std::vector<GeneralSimplex::BoundReason>& premises)
            -> std::optional<std::vector<SatLit>> {
            std::vector<SatLit> sources;
            for (const auto& premise : premises) {
                build();
                if (!premise.reason.sign || !premise.reason.var ||
                    premise.reason.var > explanations.size()) return std::nullopt;
                const auto& explanation = explanations[premise.reason.var - 1];
                if (explanation.variable != premise.var) return std::nullopt;
                include(sources, explanation.sources);
            }
            return sources;
        };
        std::vector<GeneralSimplex::ActiveBound> bounds;
        bounds.reserve(2 * constraints.size());
        std::unordered_set<uint64_t> activeReasons;
        auto reasonKey = [](SatLit literal) {
            return (static_cast<uint64_t>(literal.var) << 1) | literal.sign;
        };
        using VariableIterator = std::map<MonomialKey, int>::const_iterator;
        std::vector<VariableIterator> active;
        std::unordered_set<int> activeColumns;
        auto activate = [&](VariableIterator variable) {
            if (activeColumns.insert(variable->second).second) active.push_back(variable);
        };
        bool nonlinear = false;
        for (const auto& constraint : constraints) {
            tick();
            if (constraint.rel == Relation::Neq) {
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
                LinearRow terms;
                for (const auto& [monomial, coefficient] : constraint.poly.terms()) {
                    tick(1 + monomial.size() + mpz_sizeinbase(coefficient.get_num_mpz_t(), 2) +
                         mpz_sizeinbase(coefficient.get_den_mpz_t(), 2));
                    if (coefficient == 0) continue;
                    if (monomial.empty()) { constant += coefficient; continue; }
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
            for (const auto& [monomial, coefficient] : constraint.poly.terms()) {
                tick();
                if (coefficient == 0 || monomial.empty()) continue;
                activate(variables_.find(monomial));
                nonlinear |= monomial.size() > 1 || monomial.front().second > 1;
            }
            ++stats.constraints;
            activeReasons.insert(reasonKey(constraint.reason));
            const auto internal = label(row, {constraint.reason});
            const auto rel = constraint.rel;
            if (rel == Relation::Eq || rel == Relation::Geq || rel == Relation::Gt)
                bounds.push_back({row, true, BoundInfo(
                    BoundValue(DeltaRational(0, rel == Relation::Gt ? 1 : 0)), internal)});
            if (rel == Relation::Eq || rel == Relation::Leq || rel == Relation::Lt)
                bounds.push_back({row, false, BoundInfo(
                    BoundValue(DeltaRational(0, rel == Relation::Lt ? -1 : 0)), internal)});
        }
        auto updateStats = [&] {
            stats.variables = variables_.size();
            stats.retainedRows = simplex_.numRows();
        };
        auto liftConflict = [&]() -> std::optional<std::vector<SatLit>> {
            updateStats();
            auto sources = expand(simplex_.getConflict());
            if (!sources || sources->empty()) return std::nullopt;
            for (auto source : *sources)
                if (!activeReasons.contains(reasonKey(source))) return std::nullopt;
            return sources;
        };
        // Conditional product bounds are rebuilt from current explanations.
        // Only unconditional auxiliary definitions survive premise withdrawal.
        simplex_.replaceActiveBounds(bounds, GeneralSimplex::AssignmentPolicy::Preserve);
        std::set<std::pair<int, mpq_class>> applied;
        for (;;) {
            tick();
            updateStats();
            ++stats.closureChecks;
            const auto result = simplex_.checkUntil(deadline);
            if (result == GeneralSimplex::Result::Unknown) stats.exhausted = true;
            if (result == GeneralSimplex::Result::Unsat) return liftConflict();
            if (result != GeneralSimplex::Result::Sat || !nonlinear) return std::nullopt;
            const auto facts = simplex_.sharedFixedValueAnalysis();
            bool progress = false;
            for (size_t index = 0; index < active.size(); ++index) {
                build();
                const auto current = active[index];
                const auto& monomial = current->first;
                if (monomial.size() == 1 && monomial.front().second == 1) continue;
                struct Factor { int column, exponent; mpq_class value; };
                std::vector<Factor> fixed;
                MonomialKey remaining;
                bool zero = false;
                for (const auto& [variable, exponent] : monomial) {
                    build();
                    if (exponent <= 0) throw ResourceExhausted("invalid monomial exponent");
                    const auto base = variables_.find(MonomialKey{{variable, 1}});
                    const auto value = base == variables_.end() ? std::nullopt : facts->fixedValue(base->second);
                    if (!value || value->b != 0) { remaining.emplace_back(variable, exponent); continue; }
                    if (value->a == 0) {
                        fixed = {{base->second, exponent, mpq_class(0)}};
                        zero = true;
                        break;
                    }
                    fixed.push_back({base->second, exponent, value->a});
                }
                if (fixed.empty()) continue;
                mpq_class multiplier = zero ? 0 : 1;
                std::vector<SatLit> sources;
                bool explained = true;
                for (const auto& factor : fixed) {
                    const auto proof = facts->prove(factor.column);
                    if (!proof || proof->second.empty()) { explained = false; break; }
                    const auto parents = expand(proof->second);
                    if (!parents) { explained = false; break; }
                    include(sources, *parents);
                    if (zero) break;
                    mpq_class value;
                    if (factor.value == 1) value = 1;
                    else if (factor.value == -1) value = factor.exponent % 2 ? -1 : 1;
                    else {
                        const size_t bits = mpz_sizeinbase(factor.value.get_num_mpz_t(), 2) +
                                            mpz_sizeinbase(factor.value.get_den_mpz_t(), 2);
                        if (static_cast<size_t>(factor.exponent) > std::numeric_limits<size_t>::max() / bits)
                            throw ResourceExhausted("polynomial product coefficient allocation overflow");
                        build(bits * static_cast<size_t>(factor.exponent));
                        mpz_class numerator, denominator;
                        mpz_pow_ui(numerator.get_mpz_t(), factor.value.get_num_mpz_t(), factor.exponent);
                        mpz_pow_ui(denominator.get_mpz_t(), factor.value.get_den_mpz_t(), factor.exponent);
                        value = mpq_class(numerator, denominator);
                    }
                    build(mpz_sizeinbase(multiplier.get_num_mpz_t(), 2) +
                          mpz_sizeinbase(multiplier.get_den_mpz_t(), 2) +
                          mpz_sizeinbase(value.get_num_mpz_t(), 2) +
                          mpz_sizeinbase(value.get_den_mpz_t(), 2));
                    multiplier *= value;
                }
                if (!explained || sources.empty()) continue;
                int variable = current->second;
                mpq_class value = multiplier;
                if (!zero && !remaining.empty()) {
                    auto residual = variables_.find(remaining);
                    if (residual == variables_.end())
                        residual = variables_.emplace(remaining,
                            simplex_.addVar("m" + std::to_string(variables_.size()))).first;
                    activate(residual);
                    LinearRow terms{{current->second, mpq_class(1)}, {residual->second, -multiplier}};
                    std::sort(terms.begin(), terms.end(), [](const auto& a, const auto& b) { return a.first < b.first; });
                    auto definition = productRows_.find(terms);
                    if (definition == productRows_.end()) {
                        const int auxiliary = simplex_.addConstraint(terms, 0);
                        if (auxiliary < 0) return std::nullopt;
                        definition = productRows_.emplace(std::move(terms), auxiliary).first;
                    } else if (!applied.contains({definition->second, mpq_class(0)})) ++stats.reusedProductRows;
                    variable = definition->second;
                    value = 0;
                } else {
                    const auto existing = facts->fixedValue(variable);
                    if (existing && existing->b == 0 && existing->a == value) continue;
                }
                if (!applied.emplace(variable, value).second) continue;
                const auto reason = label(variable, std::move(sources));
                const BoundInfo exact(BoundValue(DeltaRational(value)), reason);
                ++stats.productFacts;
                progress = true;
                if (!simplex_.assertLower(variable, exact) || !simplex_.assertUpper(variable, exact)) return liftConflict();
            }
            if (!progress) { updateStats(); return std::nullopt; }
        }
    } catch (const ResourceExhausted&) {
        stats.exhausted = true;
    }
    return std::nullopt;
}

} // namespace xolver
