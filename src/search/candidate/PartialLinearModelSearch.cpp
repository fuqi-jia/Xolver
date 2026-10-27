#include "search/candidate/PartialLinearModelSearch.h"
#include "search/candidate/BoundaryCandidates.h"
#include "search/lra/GeneralSimplex.h"
#include "base/WorkBudget.h"
#include <algorithm>
#include <chrono>
#include <map>
#include <set>
#include <tuple>

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
        for (const auto& c : constraints) {
            tick();
            if (c.poly == NullPoly) return std::nullopt;
            auto terms = kernel.terms(c.poly);
            if (!terms) return std::nullopt;
            VarId unary = NullVar;
            mpq_class coefficient = 0, constant = 0;
            bool linearUnary = true;
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
                    if (!pinned.contains(var)) scores[var] += exponent;
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

        // One linear relaxation for the entire local search. Distinct nonlinear
        // monomials initially have independent columns. A parameter assignment
        // activates exact identities m = value^exponent * (m / parameter^exponent).
        // Build only the quotient chains in the fixed cover order, rather than
        // all subsets of a monomial's parameters.
        struct Link { Powers monomial, quotient; int exponent; };
        std::vector<std::map<Powers, Link>> links(parameters.size());
        std::set<Powers> closure(monomials.begin(), monomials.end());
        for (const auto& monomial : monomials) {
            Powers current = monomial;
            for (size_t depth = 0; depth < parameters.size(); ++depth) {
                tick();
                if (current.empty() || (current.size() == 1 && current[0].second == 1)) break;
                auto it = std::find_if(current.begin(), current.end(), [&](const auto& power) {
                    return power.first == parameters[depth];
                });
                if (it == current.end()) continue;
                const int exponent = it->second;
                Powers quotient = current;
                quotient.erase(quotient.begin() + (it - current.begin()));
                links[depth].try_emplace(current, Link{current, quotient, exponent});
                closure.insert(quotient);
                current = std::move(quotient);
            }
        }

        GeneralSimplex simplex;
        ++stats.contexts;
        auto check = [&]() {
            ++stats.linearChecks;
            const auto result = simplex.checkUntil(deadline);
            stats.exhausted |= result == GeneralSimplex::Result::Unknown;
            return result;
        };
        std::map<VarId, int> columns;
        std::map<Powers, int> monomialColumns;
        for (auto var : variables) {
            tick();
            columns[var] = simplex.addVar(std::string(kernel.varName(var)));
            monomialColumns[{{var, 1}}] = columns.at(var);
        }
        const auto reason = SatLit::positive(1); // private; never exported
        auto fix = [&](int column, const mpq_class& value, int level) {
            const BoundInfo bound(BoundValue(DeltaRational(value)), reason);
            return simplex.assertLower(column, bound, level) &&
                   simplex.assertUpper(column, bound, level);
        };
        const int unit = simplex.addVar("monomial-unit");
        if (!fix(unit, mpq_class(1), 0)) return std::nullopt;
        monomialColumns[{}] = unit;
        for (const auto& powers : closure) {
            tick();
            if (!monomialColumns.contains(powers))
                monomialColumns[powers] = simplex.addVar("monomial");
        }
        for (size_t index = 0; index < atoms.size(); ++index) {
            tick();
            std::map<int, mpq_class> coefficients;
            mpq_class constant = 0;
            for (const auto& term : atoms[index]) {
                tick();
                if (term.coefficient == 0) continue;
                if (term.powers.empty()) constant += term.coefficient;
                else coefficients[monomialColumns.at(term.powers)] += term.coefficient;
            }
            std::vector<std::pair<int, mpq_class>> row;
            for (const auto& [column, coefficient] : coefficients)
                if (coefficient != 0) row.emplace_back(column, coefficient);
            const auto relation = constraints[index].rel;
            if (row.empty()) {
                if (!holds(constant, relation)) return std::nullopt;
                continue;
            }
            if (relation == Relation::Neq) continue; // checked on the original model
            const int auxiliary = simplex.addConstraint(row, -constant);
            if (auxiliary < 0) return std::nullopt;
            if ((relation == Relation::Eq || relation == Relation::Gt || relation == Relation::Geq) &&
                !simplex.assertLower(auxiliary, BoundInfo(BoundValue(
                    DeltaRational(0, relation == Relation::Gt ? 1 : 0)), reason))) return std::nullopt;
            if ((relation == Relation::Eq || relation == Relation::Lt || relation == Relation::Leq) &&
                !simplex.assertUpper(auxiliary, BoundInfo(BoundValue(
                    DeltaRational(0, relation == Relation::Lt ? -1 : 0)), reason))) return std::nullopt;
        }
        if (check() != GeneralSimplex::Result::Sat) return std::nullopt;

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
        auto power = [&](const mpq_class& value, int exponent) -> mpq_class {
            if (value == 0 || value == 1) return value;
            if (value == -1) return exponent % 2 ? mpq_class(-1) : mpq_class(1);
            const size_t bits = mpz_sizeinbase(value.get_num().get_mpz_t(), 2) +
                                mpz_sizeinbase(value.get_den().get_mpz_t(), 2);
            if (bits > 100000 || static_cast<size_t>(exponent) > 100000 / bits)
                throw ResourceExhausted("partial linear model coefficient exhausted");
            budget.tick(bits * exponent);
            mpz_class numerator, denominator;
            mpz_pow_ui(numerator.get_mpz_t(), value.get_num().get_mpz_t(), exponent);
            mpz_pow_ui(denominator.get_mpz_t(), value.get_den().get_mpz_t(), exponent);
            return mpq_class(numerator, denominator);
        };
        std::map<std::tuple<int, int, mpq_class>, int> definitions;
        auto apply = [&](size_t depth, const mpq_class& value) {
            tick();
            const int level = static_cast<int>(depth) + 1;
            if (!fix(columns.at(parameters[depth]), value, level)) return false;
            for (const auto& [powers, link] : links[depth]) {
                tick();
                (void)powers;
                const int monomial = monomialColumns.at(link.monomial);
                const int quotient = monomialColumns.at(link.quotient);
                const auto factor = power(value, link.exponent);
                const auto key = std::make_tuple(monomial, quotient, factor);
                auto it = definitions.find(key);
                if (it == definitions.end()) {
                    // Only the equality bound is conditional. The row itself
                    // defines a fresh auxiliary and remains valid after pop.
                    const int auxiliary = simplex.addConstraint(
                        {{monomial, mpq_class(1)}, {quotient, -factor}}, mpq_class(0));
                    if (auxiliary < 0) return false;
                    it = definitions.emplace(key, auxiliary).first;
                    ++stats.definitions;
                }
                if (!fix(it->second, mpq_class(0), level)) return false;
            }
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
