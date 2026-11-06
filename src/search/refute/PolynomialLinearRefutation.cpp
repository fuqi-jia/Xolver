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
        struct Disequality { int variable; mpq_class excluded; SatLit reason; };
        std::vector<Disequality> disequalities;
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
            if (constraint.rel == Relation::Neq && constraint.poly.isConstant()) {
                if (constraint.poly.isZero()) {
                    ++stats.constraints;
                    return std::vector<SatLit>{constraint.reason};
                }
                continue;
            }
            auto found = rows_.find(constraint.reason.var);
            int row;
            auto rel = constraint.rel;
            mpq_class endpoint = 0;
            const auto& polynomialTerms = constraint.poly.terms();
            const bool unary = (polynomialTerms.size() == 1 && !polynomialTerms.front().first.empty()) ||
                (polynomialTerms.size() == 2 && polynomialTerms.front().first.empty());
            if (unary) {
                const auto& [monomial, coefficient] = polynomialTerms.back();
                const mpq_class constant = polynomialTerms.front().first.empty()
                    ? polynomialTerms.front().second : mpq_class(0);
                tick(1 + monomial.size() + mpz_sizeinbase(coefficient.get_num_mpz_t(), 2) +
                     mpz_sizeinbase(coefficient.get_den_mpz_t(), 2) +
                     mpz_sizeinbase(constant.get_num_mpz_t(), 2) +
                     mpz_sizeinbase(constant.get_den_mpz_t(), 2));
                auto variable = variables_.find(monomial);
                if (variable == variables_.end())
                    variable = variables_.emplace(monomial,
                        simplex_.addVar("m" + std::to_string(variables_.size()))).first;
                row = variable->second;
                endpoint = -constant / coefficient;
                if (coefficient < 0) {
                    switch (rel) {
                        case Relation::Geq: rel = Relation::Leq; break;
                        case Relation::Gt: rel = Relation::Lt; break;
                        case Relation::Leq: rel = Relation::Geq; break;
                        case Relation::Lt: rel = Relation::Gt; break;
                        default: break;
                    }
                }
                // A bound on one canonical monomial needs no defining slack
                // row. All signed sources still receive independent labels.
                if (found != rows_.end() && found->second.polynomial.terms() == polynomialTerms)
                    ++stats.reusedRows;
                else rows_.insert_or_assign(constraint.reason.var, Row{constraint.poly, row});
            } else if (found != rows_.end() &&
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
            if (rel == Relation::Neq) {
                // Keep the exact definition without imposing either strict
                // polarity. A candidate value of zero is not a contradiction;
                // only an explained fixed value can exclude every model.
                disequalities.push_back({row, endpoint, constraint.reason});
                continue;
            }
            const auto internal = label(row, {constraint.reason});
            if (rel == Relation::Eq || rel == Relation::Geq || rel == Relation::Gt)
                bounds.push_back({row, true, BoundInfo(
                    BoundValue(DeltaRational(endpoint, rel == Relation::Gt ? 1 : 0)), internal)});
            if (rel == Relation::Eq || rel == Relation::Leq || rel == Relation::Lt)
                bounds.push_back({row, false, BoundInfo(
                    BoundValue(DeltaRational(endpoint, rel == Relation::Lt ? -1 : 0)), internal)});
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
        if (!simplex_.replaceActiveBounds(bounds, GeneralSimplex::AssignmentPolicy::Preserve))
            return liftConflict();
        std::set<std::pair<int, mpq_class>> applied;
        for (;;) {
            tick();
            // Keep the lifted monomials consistent with the exact signs of
            // their factors. These are implications of active bounds, never
            // guesses from the current relaxation point. Even powers need no
            // sign premise; strict factor bounds retain their infinitesimals.
            constexpr unsigned negative = 1, zero = 2, positive = 4, any = 7;
            auto productSigns = [](unsigned left, unsigned right) {
                unsigned result = 0;
                for (const unsigned a : {negative, zero, positive})
                    for (const unsigned b : {negative, zero, positive})
                        if ((left & a) && (right & b))
                            result |= a == zero || b == zero ? zero : a == b ? positive : negative;
                return result;
            };
            for (const auto current : active) {
                const auto& monomial = current->first;
                if (monomial.size() == 1 && monomial.front().second == 1) continue;
                unsigned signs = positive;
                std::vector<SatLit> sources;
                for (const auto& [variable, exponent] : monomial) {
                    build();
                    if (exponent <= 0) throw ResourceExhausted("invalid monomial exponent");
                    unsigned factor = any;
                    const auto base = variables_.find(MonomialKey{{variable, 1}});
                    if (base != variables_.end()) {
                        const auto state = simplex_.varState(base->second);
                        auto restrict = [&](const BoundInfo& bound, bool lower) {
                            if (!bound.bound.isFinite() || !bound.reason) return;
                            const auto value = bound.bound.value;
                            if (lower ? value < DeltaRational(0) : value > DeltaRational(0)) return;
                            const auto premises = expand({{base->second, lower, *bound.reason}});
                            if (!premises) return;
                            include(sources, *premises);
                            factor &= lower ? (value > DeltaRational(0) ? positive : zero | positive)
                                            : (value < DeltaRational(0) ? negative : negative | zero);
                        };
                        restrict(state.lower, true);
                        restrict(state.upper, false);
                    }
                    if (exponent % 2 == 0)
                        factor = (factor & zero) | ((factor & (negative | positive)) ? positive : 0);
                    signs = productSigns(signs, factor);
                }
                for (const bool lower : {true, false}) {
                    if (signs & (lower ? negative : positive)) continue;
                    const DeltaRational endpoint(0, (signs & zero) ? 0 : lower ? 1 : -1);
                    const auto state = simplex_.varState(current->second);
                    const auto& previous = lower ? state.lower : state.upper;
                    if (previous.bound.isFinite() &&
                        (lower ? previous.bound.value >= endpoint : previous.bound.value <= endpoint)) continue;
                    const BoundInfo bound(BoundValue(endpoint), label(current->second, sources));
                    ++stats.signFacts;
                    const bool consistent = lower ? simplex_.assertLower(current->second, bound)
                                                  : simplex_.assertUpper(current->second, bound);
                    if (!consistent) return liftConflict();
                }
            }
            updateStats();
            ++stats.closureChecks;
            const auto result = simplex_.checkUntil(deadline);
            if (result == GeneralSimplex::Result::Unknown) stats.exhausted = true;
            if (result == GeneralSimplex::Result::Unsat) return liftConflict();
            if (result != GeneralSimplex::Result::Sat || (!nonlinear && disequalities.empty()))
                return std::nullopt;
            const auto facts = simplex_.sharedFixedValueAnalysis();
            for (const auto& disequality : disequalities) {
                tick();
                const auto value = facts->fixedValue(disequality.variable);
                if (!value || value->b != 0 || value->a != disequality.excluded) continue;
                const auto proof = facts->prove(disequality.variable);
                if (!proof) continue;
                auto sources = expand(proof->second);
                if (!sources || std::any_of(sources->begin(), sources->end(), [&](SatLit source) {
                        return !activeReasons.contains(reasonKey(source));
                    })) continue;
                include(*sources, {disequality.reason});
                return sources;
            }
            // A coupled polyhedron can force a value without fixing both
            // explicit endpoints of its tableau column. Discharge both strict
            // alternatives exactly instead of treating a zero-valued point as
            // proof. The temporary bound is local to each feasibility query.
            for (const auto& disequality : disequalities) {
                tick();
                const auto point = simplex_.value(disequality.variable);
                if (point.a != disequality.excluded || point.b != 0) continue;
                std::vector<GeneralSimplex::ActiveBound> saved;
                for (int variable = 0; variable < simplex_.numVars(); ++variable) {
                    const auto state = simplex_.varState(variable);
                    if (state.lower.bound.isFinite()) saved.push_back({variable, true, state.lower});
                    if (state.upper.bound.isFinite()) saved.push_back({variable, false, state.upper});
                }
                auto refuteSide = [&](bool lower) -> std::optional<std::vector<SatLit>> {
                    ++stats.disequalityChecks;
                    auto answer = GeneralSimplex::Result::Unknown;
                    std::optional<std::vector<SatLit>> proof;
                    try {
                        const BoundInfo hypothesis(BoundValue(DeltaRational(
                            disequality.excluded, lower ? 1 : -1)),
                            label(disequality.variable, {disequality.reason}));
                        const bool consistent = lower ? simplex_.assertLower(disequality.variable, hypothesis)
                                                      : simplex_.assertUpper(disequality.variable, hypothesis);
                        answer = consistent ? simplex_.checkUntil(deadline) : GeneralSimplex::Result::Unsat;
                        if (answer == GeneralSimplex::Result::Unsat) proof = liftConflict();
                    } catch (...) {
                        simplex_.replaceActiveBounds(saved, GeneralSimplex::AssignmentPolicy::Preserve);
                        throw;
                    }
                    simplex_.replaceActiveBounds(saved, GeneralSimplex::AssignmentPolicy::Preserve);
                    const auto restored = simplex_.checkUntil(deadline);
                    if (answer == GeneralSimplex::Result::Unknown || restored != GeneralSimplex::Result::Sat) {
                        stats.exhausted = true;
                        throw ResourceExhausted("polynomial disequality case allocation exhausted");
                    }
                    return proof;
                };
                const auto upperSide = refuteSide(true);
                if (!upperSide) continue;
                const auto lowerSide = refuteSide(false);
                if (lowerSide) {
                    auto sources = *upperSide;
                    include(sources, *lowerSide);
                    include(sources, {disequality.reason});
                    return sources;
                }
            }
            if (!nonlinear) return std::nullopt;
            bool progress = false;
            auto power = [&](const mpq_class& value, int exponent) -> mpq_class {
                if (value == 0 || value == 1) return value;
                if (value == -1) return exponent % 2 ? -1 : 1;
                const size_t bits = mpz_sizeinbase(value.get_num_mpz_t(), 2) +
                                    mpz_sizeinbase(value.get_den_mpz_t(), 2);
                if (static_cast<size_t>(exponent) > std::numeric_limits<size_t>::max() / bits)
                    throw ResourceExhausted("polynomial product coefficient allocation overflow");
                build(bits * static_cast<size_t>(exponent));
                mpz_class numerator, denominator;
                mpz_pow_ui(numerator.get_mpz_t(), value.get_num_mpz_t(), exponent);
                mpz_pow_ui(denominator.get_mpz_t(), value.get_den_mpz_t(), exponent);
                return mpq_class(numerator, denominator);
            };
            auto installProduct = [&](VariableIterator current, const MonomialKey& remaining,
                                      const mpq_class& multiplier, std::vector<SatLit> sources,
                                      bool composite) {
                if (sources.empty()) return true;
                int variable = current->second;
                mpq_class value = multiplier;
                if (multiplier != 0 && !remaining.empty()) {
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
                        if (auxiliary < 0) throw ResourceExhausted("polynomial product definition allocation failed");
                        definition = productRows_.emplace(std::move(terms), auxiliary).first;
                    } else if (!applied.contains({definition->second, mpq_class(0)})) ++stats.reusedProductRows;
                    variable = definition->second;
                    value = 0;
                } else {
                    const auto existing = facts->fixedValue(variable);
                    if (existing && existing->b == 0 && existing->a == value) return true;
                }
                if (!applied.emplace(variable, value).second) return true;
                const auto reason = label(variable, std::move(sources));
                const BoundInfo exact(BoundValue(DeltaRational(value)), reason);
                ++stats.productFacts;
                stats.monomialProducts += composite;
                progress = true;
                return simplex_.assertLower(variable, exact) && simplex_.assertUpper(variable, exact);
            };
            struct FixedMonomial { VariableIterator variable; mpq_class value; };
            std::unordered_map<VarId, std::vector<FixedMonomial>> fixedMonomials;
            for (const auto current : active) {
                build();
                const auto& monomial = current->first;
                if (monomial.size() == 1 && monomial.front().second == 1) continue;
                const auto value = facts->fixedValue(current->second);
                if (value && value->b == 0)
                    fixedMonomials[monomial.front().first].push_back({current, value->a});
            }
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
                    const mpq_class value = power(factor.value, factor.exponent);
                    build(mpz_sizeinbase(multiplier.get_num_mpz_t(), 2) +
                          mpz_sizeinbase(multiplier.get_den_mpz_t(), 2) +
                          mpz_sizeinbase(value.get_num_mpz_t(), 2) +
                          mpz_sizeinbase(value.get_den_mpz_t(), 2));
                    multiplier *= value;
                }
                if (explained && !sources.empty() &&
                    !installProduct(current, remaining, multiplier, std::move(sources), false)) return liftConflict();

                // A fixed product constrains every divisible monomial even
                // when none of its individual factors is fixed. Index by one
                // required variable instead of comparing every pair of words.
                // The identity m = c^k * (m/d^k) needs no nonzero premise.
                for (const auto& [variable, exponent] : monomial) {
                    (void)exponent;
                    const auto found = fixedMonomials.find(variable);
                    if (found == fixedMonomials.end()) continue;
                    for (const auto& factor : found->second) {
                        build();
                        if (factor.variable == current) continue;
                        ++stats.monomialDivisibilityChecks;
                        const auto& divisor = factor.variable->first;
                        int copies = std::numeric_limits<int>::max();
                        size_t position = 0;
                        for (const auto& [base, degree] : divisor) {
                            build();
                            while (position < monomial.size() && monomial[position].first < base) ++position;
                            if (degree <= 0 || position == monomial.size() || monomial[position].first != base) {
                                copies = 0;
                                break;
                            }
                            copies = std::min(copies, monomial[position].second / degree);
                        }
                        if (!copies) continue;
                        const auto proof = facts->prove(factor.variable->second);
                        if (!proof || proof->second.empty()) continue;
                        auto support = expand(proof->second);
                        if (!support || support->empty()) continue;
                        MonomialKey quotient;
                        position = 0;
                        for (const auto& [base, degree] : monomial) {
                            build();
                            int rest = degree;
                            if (position < divisor.size() && divisor[position].first == base)
                                rest -= copies * divisor[position++].second;
                            if (rest) quotient.emplace_back(base, rest);
                        }
                        if (!installProduct(current, quotient, power(factor.value, copies),
                                            std::move(*support), true)) return liftConflict();
                    }
                }
            }
            if (!progress) { updateStats(); return std::nullopt; }
        }
    } catch (const ResourceExhausted&) {
        stats.exhausted = true;
    }
    return std::nullopt;
}

std::optional<std::vector<SatLit>> refuteByPolynomialConsequences(
    PolynomialLinearRefuter& refuter, const std::vector<SignRefuteConstraint>& sources,
    const std::vector<PolynomialConsequence>& consequences,
    std::chrono::steady_clock::time_point deadline, PolynomialLinearStatistics* statistics) {
    if (statistics) *statistics = {};
    try {
        WorkBudget work(100000);
        auto tick = [&](size_t amount = 1) {
            work.tick(amount);
            if (std::chrono::steady_clock::now() >= deadline)
                throw ResourceExhausted("polynomial consequence allocation exhausted");
        };
        auto key = [](SatLit literal) { return (uint64_t(literal.var) << 1) | literal.sign; };
        std::unordered_set<uint64_t> active;
        std::vector<SignRefuteConstraint> combined;
        SatVar largest = 0;
        for (const auto& source : sources) {
            tick(1 + source.poly.terms().size());
            active.insert(key(source.reason));
            largest = std::max(largest, source.reason.var);
            combined.push_back(source);
        }
        std::unordered_map<SatVar, const std::vector<SatLit>*> explanations;
        for (const auto& consequence : consequences) {
            tick();
            bool supported = true;
            for (auto premise : consequence.premises) {
                tick();
                supported &= active.contains(key(premise));
            }
            if (!supported || largest == std::numeric_limits<SatVar>::max()) continue;
            tick(consequence.poly.terms().size());
            const auto label = SatLit::positive(++largest);
            explanations.emplace(label.var, &consequence.premises);
            combined.push_back({consequence.poly, consequence.rel, label});
        }
        auto conflict = refuter.check(combined, deadline, statistics);
        if (!conflict) return std::nullopt;
        std::vector<SatLit> lifted;
        auto append = [&](SatLit premise) {
            if (!active.contains(key(premise))) return false;
            if (std::find(lifted.begin(), lifted.end(), premise) == lifted.end()) lifted.push_back(premise);
            return true;
        };
        for (auto premise : *conflict) {
            tick();
            if (const auto found = explanations.find(premise.var); found != explanations.end()) {
                if (!premise.sign) return std::nullopt;
                for (auto source : *found->second) if (!append(source)) return std::nullopt;
            } else if (!append(premise)) return std::nullopt;
        }
        if (!lifted.empty()) return lifted;
    } catch (const ResourceExhausted&) {
        if (statistics) statistics->exhausted = true;
    }
    return std::nullopt;
}

} // namespace xolver
