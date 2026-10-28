#include "search/candidate/PartialLinearModelSearch.h"
#include "search/candidate/BoundaryCandidates.h"
#include "search/lra/GeneralSimplex.h"
#include "base/WorkBudget.h"
#include <algorithm>
#include <chrono>
#include <map>
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
    Statistics* statistics) {
    Statistics local;
    auto& stats = statistics ? *statistics : local;
    stats = {};
    try {
        const auto deadline = std::chrono::steady_clock::now() + std::chrono::milliseconds(20);
        WorkBudget budget(100000);
        auto tick = [&]() {
            budget.tick();
            if ((budget.used() & 63) == 0 && std::chrono::steady_clock::now() >= deadline)
                throw ResourceExhausted("partial linear model allocation exhausted");
        };
        using Terms = std::vector<PolynomialKernel::MonomialTerm>;
        std::vector<Terms> atoms;
        using Powers = std::vector<std::pair<VarId, int>>;
        std::vector<Powers> monomials;
        std::set<VarId> variables, pinned;
        std::vector<VarId> parameters;
        std::map<VarId, Interval> intervals;
        std::map<VarId, size_t> equalityOccurrences, otherOccurrences;
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
            auto& occurrences = c.rel == Relation::Eq ? equalityOccurrences : otherOccurrences;
            for (const auto var : support) {
                tick();
                ++occurrences[var];
            }
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

        // Keep a jointly affine block of equality unknowns. Pinning a shared
        // unknown instead samples a finite grid on an exact equality surface:
        // a*r=1, b*r=2, c*r=3 with fixed a,b,c need not have a sampled r.
        // Include inequalities in the incidence relation too, so no remaining
        // atom can contain a product of two retained unknowns. A power above
        // one always makes its variable a parameter.
        std::map<VarId, std::vector<size_t>> incidence;
        std::set<VarId> powers;
        for (size_t index = 0; index < monomials.size(); ++index)
            for (const auto& [var, exponent] : monomials[index]) {
                tick();
                incidence[var].push_back(index);
                if (exponent > 1) powers.insert(var);
            }
        std::vector<VarId> equalityUnknowns;
        for (const auto& [var, count] : equalityOccurrences) {
            tick();
            (void)count;
            if (incidence.contains(var) && !powers.contains(var)) equalityUnknowns.push_back(var);
        }
        std::sort(equalityUnknowns.begin(), equalityUnknowns.end(), [&](VarId a, VarId b) {
            if (equalityOccurrences[a] != equalityOccurrences[b])
                return equalityOccurrences[a] > equalityOccurrences[b];
            if (otherOccurrences[a] != otherOccurrences[b])
                return otherOccurrences[a] < otherOccurrences[b];
            return a < b;
        });
        std::set<VarId> retained;
        std::vector<bool> occupied(monomials.size(), false);
        for (const auto var : equalityUnknowns) {
            bool conflict = false;
            for (const auto index : incidence.at(var)) {
                tick();
                if (occupied[index]) { conflict = true; break; }
            }
            if (conflict) continue;
            retained.insert(var);
            for (const auto index : incidence.at(var)) {
                tick();
                occupied[index] = true;
            }
        }
        stats.retainedEqualityVariables = retained.size();

        // A deterministic greedy cover leaves at most one degree-one variable
        // in every monomial. Its complement can then be completed by simplex.
        for (;;) {
            std::map<VarId, size_t> scores;
            for (const auto& monomial : monomials) {
                tick();
                size_t degree = 0;
                for (const auto& [var, exponent] : monomial)
                    if (!pinned.contains(var)) degree += exponent;
                if (degree <= 1) continue;
                for (const auto& [var, exponent] : monomial)
                    if (!pinned.contains(var) && !retained.contains(var)) scores[var] += exponent;
            }
            if (scores.empty()) break;
            auto best = scores.begin();
            for (auto it = scores.begin(); it != scores.end(); ++it)
                if (it->second > best->second) best = it;
            pinned.insert(best->first);
            parameters.push_back(best->first);
        }
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
            return result;
        };
        std::map<VarId, int> columns;
        for (auto var : variables) {
            tick();
            columns[var] = simplex.addVar(std::string(kernel.varName(var)));
        }
        const auto reason = SatLit::positive(1); // private; never exported
        auto fix = [&](int column, const mpq_class& value, int level) {
            const BoundInfo bound(BoundValue(DeltaRational(value)), reason);
            return simplex.assertLower(column, bound, level) &&
                   simplex.assertUpper(column, bound, level);
        };
        Model selected;
        std::map<VarId, std::map<int, mpq_class>> selectedPowers;
        auto power = [&](VarId var, int exponent) -> mpq_class {
            auto& cache = selectedPowers[var];
            if (auto it = cache.find(exponent); it != cache.end()) return it->second;
            const auto& value = selected.at(var);
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
        std::vector<std::vector<size_t>> introduced(parameters.size() + 1);
        std::vector<std::vector<size_t>> affected(parameters.size());
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
            for (size_t depth = 0; depth < parameters.size(); ++depth) {
                tick();
                if (support.contains(parameters[depth])) affected[depth].push_back(index);
            }
        }
        auto activate = [&](const std::vector<size_t>& indices, int level) {
            for (const auto index : indices) {
                tick();
                if (active[index]) continue;
                std::map<int, mpq_class> coefficients;
                mpq_class constant = 0;
                bool affine = true;
                for (const auto& term : atoms[index]) {
                    tick();
                    mpq_class coefficient(term.coefficient);
                    Powers remaining;
                    for (const auto& [var, exponent] : term.powers) {
                        tick();
                        if (coefficient == 0) break;
                        if (selected.contains(var)) coefficient *= power(var, exponent);
                        else remaining.emplace_back(var, exponent);
                    }
                    if (coefficient == 0) continue;
                    if (remaining.empty()) constant += coefficient;
                    else if (remaining.size() == 1 && remaining[0].second == 1)
                        coefficients[columns.at(remaining[0].first)] += coefficient;
                    else { affine = false; break; }
                }
                if (!affine) continue;
                active[index] = true;
                introduced[level].push_back(index);
                Row row;
                for (const auto& [column, coefficient] : coefficients)
                    if (coefficient != 0) row.emplace_back(column, coefficient);
                const auto relation = constraints[index].rel;
                if (row.empty()) {
                    if (!holds(constant, relation)) return false;
                    continue;
                }
                if (relation == Relation::Neq) continue; // final original-model check
                const auto key = std::make_pair(row, constant);
                auto it = definitions.find(key);
                if (it == definitions.end()) {
                    const int auxiliary = simplex.addConstraint(row, -constant);
                    if (auxiliary < 0) return false;
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
        if (auto point = complete()) return point;

        auto candidates = [&](size_t depth) {
            tick();
            std::vector<mpq_class> values;
            // A retained child assignment can violate its parent's bounds.
            // Repair before taking a concrete value from this prefix.
            if (check() != GeneralSimplex::Result::Sat) return values;
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
            const auto current = simplex.value(columns.at(var));
            addRounded(mpq_class(current.a + current.b * simplex.computeSafeDelta()));
            if (b.lower && b.upper) addRounded(mpq_class((b.lower->value + b.upper->value) / 2));
            for (const int seed : {0, 1, -1}) {
                mpq_class q = seed;
                if (b.upper && q >= b.upper->value) q = b.upper->value - (b.upper->strict ? 1 : 0);
                if (b.lower && q <= b.lower->value) q = b.lower->value + (b.lower->strict ? 1 : 0);
                add(q);
            }
            return values;
        };
        auto apply = [&](size_t depth, const mpq_class& value) {
            tick();
            const int level = static_cast<int>(depth) + 1;
            selected[parameters[depth]] = value;
            if (!fix(columns.at(parameters[depth]), value, level) ||
                !activate(affected[depth], level)) return false;
            return check() == GeneralSimplex::Result::Sat;
        };
        auto push = [&](size_t depth, const mpq_class& value) {
            ++stats.choices;
            stats.maxDepth = std::max(stats.maxDepth, depth + 1);
            const bool feasible = apply(depth, value);
            stats.rejectedChoices += !feasible;
            return feasible;
        };
        auto pop = [&](size_t depth) {
            simplex.backtrackToLevel(static_cast<int>(depth), GeneralSimplex::AssignmentPolicy::Preserve);
            for (auto index : introduced[depth + 1]) active[index] = false;
            introduced[depth + 1].clear();
            selected.erase(parameters[depth]);
            selectedPowers.erase(parameters[depth]);
        };
        return searchBoundaryCandidates(parameters.size(), candidates, push, pop, complete);
    } catch (const ResourceExhausted&) {
        stats.exhausted = true;
    } catch (const std::exception&) {
        // Unsupported arithmetic and exhaustion leave the caller's search open.
    }
    return std::nullopt;
}
} // namespace xolver
