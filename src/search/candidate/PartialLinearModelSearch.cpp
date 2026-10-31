#include "search/candidate/PartialLinearModelSearch.h"
#include "search/candidate/BoundaryCandidates.h"
#include "search/candidate/CandidateDomains.h"
#include "search/candidate/WeightedGreedyCover.h"
#include "search/lra/GeneralSimplex.h"
#include "base/WorkBudget.h"
#include <algorithm>
#include <chrono>
#include <map>
#include <limits>
#include <set>

namespace xolver {
namespace {
struct Endpoint { mpq_class value; bool strict; };
struct Interval { std::optional<Endpoint> lower, upper; };

bool holds(const mpq_class& value, Relation relation) {
    switch (relation) {
        case Relation::Eq: return value == 0;
        case Relation::Neq: return value != 0;
        case Relation::Lt: return value < 0;
        case Relation::Leq: return value <= 0;
        case Relation::Gt: return value > 0;
        case Relation::Geq: return value >= 0;
    }
    return false;
}

Relation flip(Relation relation) {
    switch (relation) {
        case Relation::Lt: return Relation::Gt;
        case Relation::Leq: return Relation::Geq;
        case Relation::Gt: return Relation::Lt;
        case Relation::Geq: return Relation::Leq;
        default: return relation;
    }
}

void tighten(std::optional<Endpoint>& current, Endpoint next, bool lower) {
    if (!current || (lower ? next.value > current->value : next.value < current->value) ||
        (next.value == current->value && next.strict)) current = std::move(next);
}
} // namespace

std::optional<PartialLinearModelSearch::Model> PartialLinearModelSearch::trySolve(
    const std::vector<Constraint>& constraints, PolynomialKernel& kernel, bool integerDomain,
    Statistics* statistics, Allocation allocation) {
    Statistics local;
    auto& stats = statistics ? *statistics : local;
    stats = {};
    try {
        if (allocation.time <= std::chrono::milliseconds::zero()) {
            stats.exhausted = true;
            return std::nullopt;
        }
        auto deadline = std::chrono::steady_clock::now() + allocation.time;
        if (wall::hasDeadline())
            deadline = std::min(deadline, std::chrono::steady_clock::now() +
                std::chrono::milliseconds(wall::remainingMs()));
        WorkBudget budget(allocation.work);
        auto tick = [&]() {
            budget.tick();
            if ((budget.used() & 63) == 0 && std::chrono::steady_clock::now() >= deadline)
                throw ResourceExhausted("partial linear model allocation exhausted");
        };
        using Terms = std::vector<PolynomialKernel::MonomialTerm>;
        std::vector<Terms> atoms;
        using Powers = std::vector<std::pair<VarId, int>>;
        std::vector<Powers> monomials;
        std::set<VarId> variables;
        std::map<VarId, Interval> intervals;
        std::set<VarId> equalityVariables;
        for (const auto& c : constraints) {
            tick();
            if (c.poly == NullPoly) return std::nullopt;
            auto terms = kernel.terms(c.poly);
            if (!terms) return std::nullopt;
            VarId unary = NullVar;
            mpq_class coefficient = 0, constant = 0;
            bool linearUnary = true;
            std::set<VarId> support;
            for (auto& term : *terms) {
                tick();
                if (term.coefficient == 0) continue;
                std::sort(term.powers.begin(), term.powers.end());
                unsigned degree = 0;
                VarId previous = NullVar;
                for (const auto& [var, exponent] : term.powers) {
                    tick();
                    if (var == previous || exponent <= 0) return std::nullopt;
                    previous = var;
                    variables.insert(var);
                    support.insert(var);
                    degree += exponent;
                }
                if (degree > 1) monomials.push_back(term.powers);
                if (term.powers.empty()) constant += term.coefficient;
                else if (term.powers.size() == 1 && term.powers[0].second == 1 &&
                         (unary == NullVar || unary == term.powers[0].first)) {
                    unary = term.powers[0].first;
                    coefficient += term.coefficient;
                } else linearUnary = false;
            }
            if (c.rel == Relation::Eq)
                for (const auto var : support) { tick(); equalityVariables.insert(var); }
            if (linearUnary && unary != NullVar && coefficient != 0 && c.rel != Relation::Neq) {
                const auto relation = coefficient < 0 ? flip(c.rel) : c.rel;
                const mpq_class value = -constant / coefficient;
                auto& bounds = intervals[unary];
                if (relation == Relation::Eq || relation == Relation::Gt || relation == Relation::Geq)
                    tighten(bounds.lower, {value, relation == Relation::Gt}, true);
                if (relation == Relation::Eq || relation == Relation::Lt || relation == Relation::Leq)
                    tighten(bounds.upper, {value, relation == Relation::Lt}, false);
            }
            atoms.push_back(std::move(*terms));
        }
        if (monomials.empty()) return std::nullopt;
        stats.variables = variables.size();

        // Resolve fixed unary domains before choosing the nonlinear cover.
        // Hard-retaining high-occurrence equality variables can leave a much
        // larger sampled block and hide useful joint linear completion.
        std::map<VarId, std::vector<size_t>> incidence;
        for (size_t index = 0; index < monomials.size(); ++index)
            for (const auto& [var, exponent] : monomials[index]) {
                tick();
                (void)exponent;
                incidence[var].push_back(index);
            }
        std::set<VarId> retained;
        // Singleton domains cost no search branch. Eliminate their incidence
        // first, then minimize the remaining sampled block by weighted cover.
        auto remainingMonomials = monomials;
        std::vector<VarId> parameters;
        for (const auto& [var, bounds] : intervals) {
            tick();
            if (!bounds.lower || !bounds.upper || bounds.lower->strict || bounds.upper->strict ||
                bounds.lower->value != bounds.upper->value || !incidence.contains(var)) continue;
            bool needed = false;
            for (const auto index : incidence.at(var)) {
                tick();
                size_t degree = 0;
                for (const auto& [variable, exponent] : remainingMonomials[index]) {
                    (void)variable;
                    degree += exponent;
                }
                needed |= degree > 1;
            }
            if (!needed) continue;
            parameters.push_back(var);
            for (const auto index : incidence.at(var)) {
                tick();
                auto& monomial = remainingMonomials[index];
                if (bounds.lower->value == 0) monomial.clear();
                else std::erase_if(monomial, [&](const auto& power) { return power.first == var; });
            }
        }
        auto cover = greedyWeightedCover(remainingMonomials, retained, tick);
        if (!cover) return std::nullopt;
        parameters.insert(parameters.end(), cover->begin(), cover->end());
        const std::set<VarId> sampled(parameters.begin(), parameters.end());
        for (const auto variable : equalityVariables)
            if (incidence.contains(variable) && !sampled.contains(variable)) retained.insert(variable);
        stats.retainedEqualityVariables = retained.size();
        stats.parameters = parameters.size();

        // Convert endpoints to the client's domain. Open real endpoints are
        // not candidates; integer endpoints are rounded with their strictness.
        for (auto& [var, bounds] : intervals) {
            (void)var;
            if (!integerDomain) continue;
            if (bounds.lower) {
                mpz_class value;
                const auto& q = bounds.lower->value;
                if (bounds.lower->strict) {
                    mpz_fdiv_q(value.get_mpz_t(), q.get_num().get_mpz_t(), q.get_den().get_mpz_t());
                    ++value;
                } else mpz_cdiv_q(value.get_mpz_t(), q.get_num().get_mpz_t(), q.get_den().get_mpz_t());
                bounds.lower = Endpoint{mpq_class(value), false};
            }
            if (bounds.upper) {
                mpz_class value;
                const auto& q = bounds.upper->value;
                if (bounds.upper->strict) {
                    mpz_cdiv_q(value.get_mpz_t(), q.get_num().get_mpz_t(), q.get_den().get_mpz_t());
                    --value;
                } else mpz_fdiv_q(value.get_mpz_t(), q.get_num().get_mpz_t(), q.get_den().get_mpz_t());
                bounds.upper = Endpoint{mpq_class(value), false};
            }
        }
        auto admissible = [&](VarId var, const mpq_class& q) {
            const auto& b = intervals[var];
            return (!integerDomain || q.get_den() == 1) &&
                (!b.lower || q > b.lower->value || (q == b.lower->value && !b.lower->strict)) &&
                (!b.upper || q < b.upper->value || (q == b.upper->value && !b.upper->strict));
        };

        // Keep one local affine context. A nonlinear atom enters it only once
        // substitution of the current prefix makes the WHOLE atom affine.
        // Omitting an unfinished atom weakens the local relaxation. This avoids
        // constructing a tableau column for every intermediate monomial.
        GeneralSimplex simplex;
        ++stats.contexts;
        auto check = [&]() {
            ++stats.linearChecks;
            const auto result = simplex.checkUntil(deadline);
            stats.exhausted |= result == GeneralSimplex::Result::Unknown;
            if (result == GeneralSimplex::Result::Unknown)
                throw ResourceExhausted("partial linear feasibility allocation exhausted");
            return result;
        };
        std::map<VarId, int> columns;
        for (auto var : variables) {
            tick();
            columns[var] = simplex.addVar(std::string(kernel.varName(var)));
        }
        if (parameters.size() > static_cast<size_t>(std::numeric_limits<int>::max()) ||
            parameters.size() >= std::numeric_limits<SatVar>::max() ||
            atoms.size() >= std::numeric_limits<SatVar>::max() - parameters.size()) return std::nullopt;
        // These private IDs distinguish parameter choices from original atoms;
        // they never enter the caller's SAT solver or escape as a refutation.
        auto fix = [&](int column, const mpq_class& value, size_t depth) {
            const BoundInfo bound(BoundValue(DeltaRational(value)),
                                  SatLit::positive(static_cast<SatVar>(depth + 1)));
            const int level = static_cast<int>(depth) + 1;
            return simplex.assertLower(column, bound, level) &&
                   simplex.assertUpper(column, bound, level);
        };
        Model selected, implied;
        std::map<VarId, std::vector<size_t>> impliedReasons;
        auto known = [&](VarId var) { return selected.contains(var) || implied.contains(var); };
        auto valueOf = [&](VarId var) -> const mpq_class& {
            if (selected.contains(var)) return selected.at(var);
            return implied.at(var);
        };
        std::map<VarId, std::map<int, mpq_class>> selectedPowers;
        auto power = [&](VarId var, int exponent) -> mpq_class {
            auto& cache = selectedPowers[var];
            if (auto it = cache.find(exponent); it != cache.end()) return it->second;
            const auto& value = valueOf(var);
            mpq_class result;
            if (exponent == 1 || value == 0 || value == 1) result = value;
            else if (value == -1) result = exponent % 2 ? -1 : 1;
            else {
                const size_t bits = mpz_sizeinbase(value.get_num().get_mpz_t(), 2) +
                                    mpz_sizeinbase(value.get_den().get_mpz_t(), 2);
                if (bits > 100000 || static_cast<size_t>(exponent) > 100000 / bits)
                    throw ResourceExhausted("partial linear model coefficient exhausted");
                budget.tick(bits * exponent);
                mpz_class numerator, denominator;
                mpz_pow_ui(numerator.get_mpz_t(), value.get_num().get_mpz_t(), exponent);
                mpz_pow_ui(denominator.get_mpz_t(), value.get_den().get_mpz_t(), exponent);
                result = mpq_class(numerator, denominator);
            }
            cache.emplace(exponent, result);
            return result;
        };
        using Row = std::vector<std::pair<int, mpq_class>>;
        std::map<std::pair<Row, mpq_class>, int> definitions;
        std::vector<bool> active(atoms.size(), false);
        size_t activeCount = 0;
        std::vector<std::vector<size_t>> atomDependencies(atoms.size());
        std::optional<std::vector<size_t>> directConflict;
        std::vector<std::vector<size_t>> introduced(parameters.size() + 1);
        std::map<VarId, size_t> parameterDepth;
        for (size_t depth = 0; depth < parameters.size(); ++depth) {
            tick();
            parameterDepth.emplace(parameters[depth], depth);
        }
        std::map<VarId, std::vector<size_t>> variableAtoms;
        auto knowledgeDependencies = [&](VarId var) {
            if (impliedReasons.contains(var) && (!selected.contains(var) || selected.at(var) == implied.at(var)))
                return impliedReasons.at(var);
            return std::vector<size_t>{parameterDepth.at(var)};
        };
        std::vector<size_t> all;
        for (size_t index = 0; index < atoms.size(); ++index) {
            tick();
            all.push_back(index);
            std::set<VarId> support;
            for (const auto& term : atoms[index])
                for (const auto& [var, exponent] : term.powers) {
                    tick();
                    (void)exponent;
                    support.insert(var);
                }
            for (const auto var : support) {
                tick();
                variableAtoms[var].push_back(index);
            }
        }
        auto fullPrefix = [&]() {
            std::vector<size_t> dependencies;
            for (size_t depth = 0; depth < selected.size(); ++depth) dependencies.push_back(depth);
            return dependencies;
        };
        auto premiseDependencies = [&](const std::vector<GeneralSimplex::BoundReason>& premises) {
            std::set<size_t> dependencies;
            bool explained = true;
            for (const auto& bound : premises) {
                tick();
                const size_t id = bound.reason.var;
                if (!bound.reason.sign || !id) { explained = false; break; }
                if (id <= parameters.size()) {
                    const size_t depth = id - 1;
                    if (!selected.contains(parameters[depth])) { explained = false; break; }
                    dependencies.insert(depth);
                } else {
                    const size_t index = id - parameters.size() - 1;
                    if (index >= atoms.size() || !active[index]) { explained = false; break; }
                    dependencies.insert(atomDependencies[index].begin(), atomDependencies[index].end());
                }
            }
            if (!explained) {
                ++stats.explanationFallbacks;
                return fullPrefix();
            }
            return std::vector<size_t>(dependencies.begin(), dependencies.end());
        };
        auto conflictDependencies = [&]() {
            if (simplex.getConflict().empty()) {
                ++stats.explanationFallbacks;
                return fullPrefix();
            }
            return premiseDependencies(simplex.getConflict());
        };
        auto activate = [&](const std::vector<size_t>& indices, int level) {
            for (const auto index : indices) {
                tick();
                if (active[index]) continue;
                std::map<int, mpq_class> coefficients;
                mpq_class constant = 0;
                bool affine = true;
                std::set<size_t> rowDependencies;
                std::map<Powers, mpq_class> residual;
                for (const auto& term : atoms[index]) {
                    tick();
                    mpq_class coefficient(term.coefficient);
                    Powers remaining;
                    std::set<size_t> termDependencies;
                    for (const auto& [var, exponent] : term.powers) {
                        tick();
                        if (coefficient == 0) break;
                        if (known(var)) {
                            const auto dependencies = knowledgeDependencies(var);
                            if (valueOf(var) == 0) {
                                coefficient = 0;
                                termDependencies.clear();
                                termDependencies.insert(dependencies.begin(), dependencies.end());
                            } else {
                                coefficient *= power(var, exponent);
                                termDependencies.insert(dependencies.begin(), dependencies.end());
                            }
                        } else remaining.emplace_back(var, exponent);
                    }
                    rowDependencies.insert(termDependencies.begin(), termDependencies.end());
                    if (coefficient == 0) continue;
                    residual[remaining] += coefficient;
                }
                for (const auto& [remaining, coefficient] : residual) {
                    tick();
                    if (coefficient == 0) continue;
                    if (remaining.empty()) constant += coefficient;
                    else if (remaining.size() == 1 && remaining[0].second == 1)
                        coefficients[columns.at(remaining[0].first)] += coefficient;
                    else { affine = false; break; }
                }
                if (!affine) continue;
                active[index] = true;
                ++activeCount;
                stats.maxActiveAtoms = std::max(stats.maxActiveAtoms, activeCount);
                introduced[level].push_back(index);
                auto& dependencies = atomDependencies[index];
                dependencies.assign(rowDependencies.begin(), rowDependencies.end());
                const auto reason = SatLit::positive(static_cast<SatVar>(parameters.size() + index + 1));
                Row row;
                for (const auto& [column, coefficient] : coefficients)
                    if (coefficient != 0) row.emplace_back(column, coefficient);
                const auto relation = constraints[index].rel;
                if (row.empty()) {
                    if (!holds(constant, relation)) {
                        directConflict = dependencies;
                        return false;
                    }
                    continue;
                }
                if (relation == Relation::Neq) continue; // final original-model check
                const auto key = std::make_pair(row, constant);
                auto it = definitions.find(key);
                if (it == definitions.end()) {
                    const int auxiliary = simplex.addConstraint(row, -constant);
                    if (auxiliary < 0)
                        throw ResourceExhausted("partial linear row registration failed");
                    it = definitions.emplace(key, auxiliary).first;
                    ++stats.definitions;
                }
                const int auxiliary = it->second;
                if ((relation == Relation::Eq || relation == Relation::Gt || relation == Relation::Geq) &&
                    !simplex.assertLower(auxiliary, BoundInfo(BoundValue(
                        DeltaRational(0, relation == Relation::Gt ? 1 : 0)), reason), level)) return false;
                if ((relation == Relation::Eq || relation == Relation::Lt || relation == Relation::Leq) &&
                    !simplex.assertUpper(auxiliary, BoundInfo(BoundValue(
                        DeltaRational(0, relation == Relation::Lt ? -1 : 0)), reason), level)) return false;
            }
            return true;
        };
        if (!activate(all, 0) || check() != GeneralSimplex::Result::Sat) return std::nullopt;

        auto complete = [&]() -> std::optional<Model> {
            tick();
            ++stats.modelChecks;
            Model point;
            const auto delta = simplex.computeSafeDelta();
            for (const auto& [var, column] : columns) {
                const auto value = simplex.value(column);
                point.emplace(var, value.a + value.b * delta);
            }
            if (integerDomain)
                for (const auto& [var, q] : point) {
                    (void)var;
                    if (q.get_den() != 1) return std::nullopt;
                }
            for (const auto& constraint : constraints) {
                tick();
                const int sign = kernel.sgnVarId(constraint.poly, point);
                if (!holds(mpq_class(sign), constraint.rel)) return std::nullopt;
            }
            return point;
        };
        auto propagateFixed = [&](int level) {
            for (;;) {
                tick();
                ++stats.propagationRounds;
                if (check() != GeneralSimplex::Result::Sat)
                    return CandidatePropagation::reject(conflictDependencies());
                const auto facts = simplex.sharedFixedValueAnalysis();
                std::set<size_t> affectedAtoms;
                for (const auto& [var, column] : columns) {
                    tick();
                    if (known(var)) continue;
                    const auto value = facts->fixedValue(column);
                    if (!value || value->b != 0) continue;
                    const auto proof = facts->prove(column);
                    if (!proof) throw ResourceExhausted("missing local singleton explanation");
                    implied.emplace(var, value->a);
                    impliedReasons.emplace(var, premiseDependencies(proof->second));
                    selectedPowers.erase(var);
                    ++stats.propagatedFacts;
                    const auto& indices = variableAtoms.at(var);
                    affectedAtoms.insert(indices.begin(), indices.end());
                }
                if (affectedAtoms.empty()) break;
                directConflict.reset();
                if (!activate(std::vector<size_t>(affectedAtoms.begin(), affectedAtoms.end()), level)) {
                    if (directConflict) return CandidatePropagation::reject(*directConflict);
                    return CandidatePropagation::reject(conflictDependencies());
                }
            }
            return CandidatePropagation::accept(activeCount == atoms.size());
        };
        if (auto point = complete()) return point;
        const auto rootProgress = propagateFixed(0);
        if (rootProgress.conflict) return std::nullopt;
        if (rootProgress.completionPossible)
            if (auto point = complete()) return point;

        Model rootAnchor;
        const auto rootDelta = simplex.computeSafeDelta();
        for (const auto& [var, column] : columns) {
            tick();
            const auto value = simplex.value(column);
            rootAnchor.emplace(var, mpq_class(value.a + value.b * rootDelta));
        }
        auto buildValues = [&](size_t depth) {
            tick();
            std::vector<mpq_class> values;
            // A retained child assignment can violate its parent's bounds.
            // Repair before taking a concrete value from this prefix.
            if (check() != GeneralSimplex::Result::Sat)
                return CandidateChoices<mpq_class>{{}, conflictDependencies()};
            const auto var = parameters[depth];
            const auto& b = intervals[var];
            auto add = [&](const mpq_class& value) {
                if (admissible(var, value) &&
                    std::find(values.begin(), values.end(), value) == values.end()) values.push_back(value);
            };
            auto addRounded = [&](const mpq_class& value) {
                if (!integerDomain) { add(value); return; }
                mpz_class floor, ceil;
                mpz_fdiv_q(floor.get_mpz_t(), value.get_num().get_mpz_t(), value.get_den().get_mpz_t());
                mpz_cdiv_q(ceil.get_mpz_t(), value.get_num().get_mpz_t(), value.get_den().get_mpz_t());
                add(mpq_class(floor));
                add(mpq_class(ceil));
            };
            std::optional<mpq_class> lower, upper;
            if (b.lower && !b.lower->strict) lower = b.lower->value;
            if (b.upper && !b.upper->strict) upper = b.upper->value;
            for (const auto& endpoint : boundaryCandidates(lower, upper)) add(endpoint);
            addRounded(rootAnchor.at(var));
            std::vector<size_t> dependencies;
            if (b.lower && b.upper) addRounded(mpq_class((b.lower->value + b.upper->value) / 2));
            for (const int seed : {0, 1, -1}) {
                mpq_class q = seed;
                if (b.upper && q >= b.upper->value) q = b.upper->value - (b.upper->strict ? 1 : 0);
                if (b.lower && q <= b.lower->value) q = b.lower->value + (b.lower->strict ? 1 : 0);
                add(q);
            }
            // This domain is frozen before any prefix choice of this pass.
            return CandidateChoices<mpq_class>{std::move(values), std::move(dependencies)};
        };
        std::vector<std::vector<mpq_class>> seeds(parameters.size());
        for (size_t depth = 0; depth < parameters.size(); ++depth)
            seeds[depth] = buildValues(depth).values;
        CandidateDomains<mpq_class> domains(std::move(seeds));
        auto pass = domains.snapshot();
        auto candidates = [&](size_t depth) {
            tick();
            auto propagated = propagateFixed(static_cast<int>(depth));
            if (propagated.conflict) return CandidateChoices<mpq_class>{{}, std::move(*propagated.conflict)};
            const auto var = parameters[depth];
            const auto current = simplex.value(columns.at(var));
            const mpq_class value = current.a + current.b * simplex.computeSafeDelta();
            auto suggest = [&](const mpq_class& q) {
                tick();
                if (admissible(var, q)) domains.suggest(depth, q, tick);
            };
            if (!integerDomain) suggest(value);
            else {
                mpz_class floor, ceil;
                mpz_fdiv_q(floor.get_mpz_t(), value.get_num().get_mpz_t(), value.get_den().get_mpz_t());
                mpz_cdiv_q(ceil.get_mpz_t(), value.get_num().get_mpz_t(), value.get_den().get_mpz_t());
                suggest(mpq_class(floor)); suggest(mpq_class(ceil));
            }
            return CandidateChoices<mpq_class>{pass.values(depth), {}, propagated.completionPossible};
        };
        auto apply = [&](size_t depth, const mpq_class& value) {
            tick();
            const int level = static_cast<int>(depth) + 1;
            const auto var = parameters[depth];
            selected[var] = value;
            if (implied.contains(var) && implied.at(var) != value) {
                auto dependencies = impliedReasons.at(var);
                dependencies.push_back(depth);
                return CandidatePropagation::reject(std::move(dependencies));
            }
            directConflict.reset();
            if (!fix(columns.at(var), value, depth) || check() != GeneralSimplex::Result::Sat)
                return CandidatePropagation::reject(conflictDependencies());
            if (!activate(variableAtoms.at(var), level)) {
                if (directConflict) return CandidatePropagation::reject(*directConflict);
                return CandidatePropagation::reject(conflictDependencies());
            }
            auto propagated = propagateFixed(level);
            return propagated;
        };
        auto push = [&](size_t depth, const mpq_class& value) {
            ++stats.choices;
            stats.maxDepth = std::max(stats.maxDepth, depth + 1);
            auto result = apply(depth, value);
            stats.rejectedChoices += result.conflict.has_value();
            return result;
        };
        auto pop = [&](size_t depth) {
            simplex.backtrackToLevel(static_cast<int>(depth), GeneralSimplex::AssignmentPolicy::Preserve);
            for (auto index : introduced[depth + 1]) {
                active[index] = false;
                --activeCount;
                atomDependencies[index].clear();
            }
            introduced[depth + 1].clear();
            selected.erase(parameters[depth]);
            implied.clear();
            impliedReasons.clear();
            selectedPowers.clear();
        };
        CandidateSearchStatistics traversal;
        auto recordTraversal = [&]() {
            stats.backjumps += traversal.backjumps;
            stats.skippedLevels += traversal.skippedLevels;
            traversal = {};
        };
        try {
            for (;;) {
                pass = domains.snapshot();
                auto result = searchBoundaryCandidates(parameters.size(), candidates, push, pop, complete, &traversal);
                recordTraversal();
                if (result) return result;
                if (!domains.refine(tick)) return std::nullopt;
                ++stats.refinements;
            }
        } catch (...) {
            recordTraversal();
            throw;
        }
    } catch (const ResourceExhausted&) {
        stats.exhausted = true;
    } catch (const std::exception&) {
        // Unsupported arithmetic and exhaustion leave the caller's search open.
    }
    return std::nullopt;
}
} // namespace xolver
