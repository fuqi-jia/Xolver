#include "search/linear/IntegerAffineModel.h"
#include "search/presolve/IntegerLinearAlgebra.h"

#include <algorithm>
#include <map>
#include <set>
#include <unordered_map>

namespace xolver {

std::optional<IntegerPoint> findIntegerAffineModel(
    const std::vector<NormalizedConstraint>& constraints, const IntegerPoint& seed) {
    std::set<std::string> names;
    size_t equations = 0;
    for (const auto& constraint : constraints) {
        if (constraint.rhs.get_den() != 1) return std::nullopt;
        for (const auto& [name, coefficient] : constraint.lhs.terms) {
            if (coefficient.get_den() != 1) return std::nullopt;
            if (constraint.rel == Relation::Eq && coefficient != 0) names.insert(name);
        }
        if (constraint.rel == Relation::Eq) ++equations;
    }
    // Rank cannot exceed the number of equations. Avoid constructing a dense
    // transform when it cannot reduce to a point or a line.
    if (names.empty() || equations + 1 < names.size()) return std::nullopt;
    std::vector<std::string> variables(names.begin(), names.end());
    std::map<std::string, size_t> columns;
    for (size_t i = 0; i < variables.size(); ++i) columns[variables[i]] = i;
    IntMatrix matrix;
    std::vector<mpz_class> rhs;
    for (const auto& constraint : constraints) {
        if (constraint.rel != Relation::Eq) continue;
        std::vector<mpz_class> row(variables.size());
        for (const auto& [name, coefficient] : constraint.lhs.terms)
            if (coefficient != 0) row[columns.at(name)] += coefficient.get_num();
        matrix.push_back(std::move(row));
        rhs.push_back(constraint.rhs.get_num());
    }
    const auto snf = smithNormalForm(matrix);
    if (variables.size() - snf.rank > 1) return std::nullopt;
    const auto transformed = matVec(snf.U, rhs);
    std::vector<mpz_class> coordinates(variables.size());
    for (int i = 0; i < snf.m; ++i) {
        if (i < snf.rank) {
            if (transformed[i] % snf.D[i][i] != 0) return std::nullopt;
            coordinates[i] = transformed[i] / snf.D[i][i];
        } else if (transformed[i] != 0) return std::nullopt;
    }
    const auto origin = matVec(snf.V, coordinates);
    std::vector<mpz_class> direction(variables.size());
    if (snf.rank < snf.n)
        for (int i = 0; i < snf.n; ++i) direction[i] = snf.V[i][snf.rank];
    if (matVec(matrix, origin) != rhs) return std::nullopt;
    for (const auto& value : matVec(matrix, direction))
        if (value != 0) return std::nullopt;

    IntegerPoint point = seed;
    for (size_t i = 0; i < variables.size(); ++i) point[variables[i]] = mpq_class(origin[i]);
    std::optional<mpz_class> lower, upper;
    std::set<mpz_class> excluded;
    auto restrictLower = [&](const mpz_class& bound) {
        if (!lower || bound > *lower) lower = bound;
    };
    auto restrictUpper = [&](const mpz_class& bound) {
        if (!upper || bound < *upper) upper = bound;
    };
    for (const auto& constraint : constraints) {
        mpq_class constant = 0, slope = 0;
        for (const auto& [name, coefficient] : constraint.lhs.terms) {
            if (coefficient == 0) continue;
            const auto value = point.find(name);
            if (value == point.end() || value->second.get_den() != 1) return std::nullopt;
            constant += coefficient * value->second;
            const auto column = columns.find(name);
            if (column != columns.end()) slope += coefficient * direction[column->second];
        }
        const mpq_class residual = constraint.rhs - constant;
        if (slope == 0) {
            const bool holds = constraint.rel == Relation::Eq ? residual == 0
                : constraint.rel == Relation::Neq ? residual != 0
                : constraint.rel == Relation::Leq && residual >= 0;
            if (!holds) return std::nullopt;
            continue;
        }
        const mpq_class bound = residual / slope;
        if (constraint.rel == Relation::Eq) {
            if (bound.get_den() != 1) return std::nullopt;
            restrictLower(bound.get_num()); restrictUpper(bound.get_num());
        } else if (constraint.rel == Relation::Neq) {
            if (bound.get_den() == 1) excluded.insert(bound.get_num());
        } else if (constraint.rel == Relation::Leq) {
            mpz_class endpoint;
            if (slope > 0) {
                mpz_fdiv_q(endpoint.get_mpz_t(), bound.get_num().get_mpz_t(), bound.get_den().get_mpz_t());
                restrictUpper(endpoint);
            } else {
                mpz_cdiv_q(endpoint.get_mpz_t(), bound.get_num().get_mpz_t(), bound.get_den().get_mpz_t());
                restrictLower(endpoint);
            }
        } else return std::nullopt;
    }
    if (lower && upper && *lower > *upper) return std::nullopt;
    mpz_class parameter = lower ? *lower : upper ? *upper : mpz_class(0);
    while (excluded.contains(parameter)) {
        if (lower || !upper) ++parameter;
        else --parameter;
    }
    if ((lower && parameter < *lower) || (upper && parameter > *upper)) return std::nullopt;
    for (size_t i = 0; i < variables.size(); ++i)
        point[variables[i]] = mpq_class(origin[i] + direction[i] * parameter);
    // Validate the original normalized constraints independently of the
    // parameter bounds. No candidate, transform or rounding is trusted alone.
    for (const auto& constraint : constraints) {
        mpq_class value = 0;
        for (const auto& [name, coefficient] : constraint.lhs.terms) {
            const auto entry = point.find(name);
            if (entry == point.end() || entry->second.get_den() != 1) return std::nullopt;
            value += coefficient * entry->second;
        }
        const bool holds = constraint.rel == Relation::Eq ? value == constraint.rhs
            : constraint.rel == Relation::Neq ? value != constraint.rhs
            : constraint.rel == Relation::Leq && value <= constraint.rhs;
        if (!holds) return std::nullopt;
    }
    return point;
}

namespace {
using Coefficients = std::map<std::string, mpq_class>;
struct RepairEquation {
    std::string pivot;
    Coefficients terms;
    mpq_class rhs;
};
struct RepairConstraint {
    Coefficients terms;
    Relation relation;
    mpq_class rhs, norm;
};

mpq_class violation(const RepairConstraint& row, const mpq_class& value) {
    if (row.relation == Relation::Eq) return abs(value - row.rhs) / row.norm;
    if (row.relation == Relation::Neq) return mpq_class(value == row.rhs) / row.norm;
    return value > row.rhs ? mpq_class((value - row.rhs) / row.norm) : mpq_class(0);
}
}

std::optional<IntegerPoint> repairIntegerAffineModel(
    const std::vector<NormalizedConstraint>& constraints,
    const IntegerPoint& relaxation, WorkBudget& budget) {
    try {
        std::vector<RepairEquation> equations;
        std::unordered_map<std::string, size_t> pivots;
        auto reduce = [&](Coefficients& terms, mpq_class& rhs) {
            for (;;) {
                size_t next = equations.size();
                for (const auto& [name, coefficient] : terms) {
                    (void)coefficient;
                    budget.tick();
                    const auto found = pivots.find(name);
                    if (found != pivots.end()) next = std::min(next, found->second);
                }
                if (next == equations.size()) break;
                const auto& equation = equations[next];
                const mpq_class factor = terms.at(equation.pivot);
                terms.erase(equation.pivot);
                rhs -= factor * equation.rhs;
                for (const auto& [name, coefficient] : equation.terms) {
                    budget.tick();
                    auto& value = terms[name];
                    value -= factor * coefficient;
                    if (value == 0) terms.erase(name);
                }
            }
        };
        auto coefficients = [&](const LinearFormKey& form) {
            Coefficients terms;
            for (const auto& [name, coefficient] : form.terms) {
                budget.tick();
                if (!relaxation.contains(name) || coefficient.get_den() != 1)
                    throw ResourceExhausted("unsupported integer repair coordinate");
                terms[name] += coefficient;
                if (terms[name] == 0) terms.erase(name);
            }
            return terms;
        };
        for (const auto& source : constraints) {
            budget.tick();
            if (source.rhs.get_den() != 1) return std::nullopt;
            if (source.rel != Relation::Eq) continue;
            auto terms = coefficients(source.lhs);
            mpq_class rhs = source.rhs;
            reduce(terms, rhs);
            if (terms.empty()) {
                if (rhs != 0) return std::nullopt;
                continue;
            }
            auto chosen = terms.end();
            for (auto it = terms.begin(); it != terms.end(); ++it) {
                budget.tick();
                if (it->second != 1 && it->second != -1) continue;
                if (chosen == terms.end()) chosen = it;
                if (relaxation.at(it->first).get_den() != 1) { chosen = it; break; }
            }
            // Non-unit equations remain in the validation/search constraints;
            // omitting them from this substitution basis is only a relaxation.
            if (chosen == terms.end()) continue;
            const auto name = chosen->first;
            const mpq_class unit = chosen->second;
            terms.erase(chosen);
            rhs /= unit;
            for (auto& [variable, coefficient] : terms) {
                (void)variable;
                coefficient /= unit;
            }
            pivots.emplace(name, equations.size());
            equations.push_back({name, std::move(terms), std::move(rhs)});
        }

        std::vector<RepairConstraint> rows;
        std::map<std::string, std::vector<std::pair<size_t, mpq_class>>> incidence;
        for (const auto& source : constraints) {
            budget.tick();
            if (source.rel != Relation::Eq && source.rel != Relation::Neq && source.rel != Relation::Leq)
                return std::nullopt;
            auto terms = coefficients(source.lhs);
            mpq_class rhs = source.rhs;
            reduce(terms, rhs);
            if (terms.empty()) {
                const bool holds = source.rel == Relation::Eq ? rhs == 0
                    : source.rel == Relation::Neq ? rhs != 0 : rhs >= 0;
                if (!holds) return std::nullopt;
                continue;
            }
            mpz_class divisor = 0;
            for (const auto& [name, coefficient] : terms) {
                (void)name;
                budget.tick();
                mpz_gcd(divisor.get_mpz_t(), divisor.get_mpz_t(), coefficient.get_num_mpz_t());
            }
            rhs /= divisor;
            if (source.rel == Relation::Leq) {
                mpz_class bound;
                mpz_fdiv_q(bound.get_mpz_t(), rhs.get_num_mpz_t(), rhs.get_den_mpz_t());
                rhs = mpq_class(bound);
            }
            mpq_class norm = 0;
            for (auto& [name, coefficient] : terms) {
                budget.tick();
                coefficient /= divisor;
                const mpq_class magnitude = abs(coefficient);
                if (magnitude > norm) norm = magnitude;
                incidence[name].emplace_back(rows.size(), coefficient);
            }
            rows.push_back({std::move(terms), source.rel, std::move(rhs), std::move(norm)});
        }
        IntegerPoint free;
        std::vector<mpq_class> values, costs;
        mpq_class score;
        for (int mode = 0; mode < 3; ++mode) {
            IntegerPoint trial;
            for (const auto& [name, value] : relaxation) {
                budget.tick();
                mpz_class integer;
                const mpq_class shifted = mode == 2 ? mpq_class(value + mpq_class(1, 2)) : value;
                if (mode == 1) mpz_cdiv_q(integer.get_mpz_t(), shifted.get_num_mpz_t(), shifted.get_den_mpz_t());
                else mpz_fdiv_q(integer.get_mpz_t(), shifted.get_num_mpz_t(), shifted.get_den_mpz_t());
                trial.emplace(name, mpq_class(integer));
            }
            std::vector<mpq_class> trialValues, trialCosts;
            mpq_class trialScore = 0;
            for (const auto& row : rows) {
                mpq_class value = 0;
                for (const auto& [name, coefficient] : row.terms) {
                    budget.tick();
                    value += coefficient * trial.at(name);
                }
                trialValues.push_back(value);
                trialCosts.push_back(violation(row, value));
                trialScore += trialCosts.back();
            }
            if (mode == 0 || trialScore < score) {
                free = std::move(trial); values = std::move(trialValues);
                costs = std::move(trialCosts); score = std::move(trialScore);
            }
        }
        while (score != 0) {
            std::set<std::string> candidates;
            for (size_t i = 0; i < rows.size(); ++i) {
                budget.tick();
                if (costs[i] == 0) continue;
                for (const auto& [name, coefficient] : rows[i].terms) {
                    (void)coefficient;
                    candidates.insert(name);
                }
            }
            mpq_class best = score, chosenValue;
            std::optional<std::string> chosen;
            for (const auto& name : candidates) {
                const auto& uses = incidence.at(name);
                std::set<mpz_class> boundaries;
                for (const auto& [i, coefficient] : uses) {
                    budget.tick();
                    const mpq_class boundary = free.at(name) + (rows[i].rhs - values[i]) / coefficient;
                    mpz_class lower, upper;
                    mpz_fdiv_q(lower.get_mpz_t(), boundary.get_num_mpz_t(), boundary.get_den_mpz_t());
                    mpz_cdiv_q(upper.get_mpz_t(), boundary.get_num_mpz_t(), boundary.get_den_mpz_t());
                    boundaries.insert(lower); boundaries.insert(upper);
                    if (rows[i].relation == Relation::Neq) {
                        boundaries.insert(mpz_class(lower - 1)); boundaries.insert(mpz_class(upper + 1));
                    }
                }
                for (const auto& value : boundaries) {
                    const mpq_class delta = mpq_class(value) - free.at(name);
                    if (delta == 0) continue;
                    mpq_class trialScore = score;
                    for (const auto& [i, coefficient] : uses) {
                        budget.tick();
                        trialScore += violation(rows[i], mpq_class(values[i] + delta * coefficient)) - costs[i];
                    }
                    if (trialScore < best) { best = std::move(trialScore); chosen = name; chosenValue = mpq_class(value); }
                }
            }
            if (!chosen) return std::nullopt;
            const mpq_class delta = chosenValue - free.at(*chosen);
            free.at(*chosen) = chosenValue;
            for (const auto& [i, coefficient] : incidence.at(*chosen)) {
                budget.tick();
                values[i] += delta * coefficient;
                costs[i] = violation(rows[i], values[i]);
            }
            score = std::move(best);
        }
        for (auto it = equations.rbegin(); it != equations.rend(); ++it) {
            mpq_class value = it->rhs;
            for (const auto& [name, coefficient] : it->terms) {
                budget.tick();
                value -= coefficient * free.at(name);
            }
            free.at(it->pivot) = std::move(value);
        }
        for (const auto& [name, value] : free) {
            (void)name;
            budget.tick();
            if (value.get_den() != 1) return std::nullopt;
        }
        for (const auto& source : constraints) {
            mpq_class value = 0;
            for (const auto& [name, coefficient] : source.lhs.terms) {
                budget.tick();
                value += coefficient * free.at(name);
            }
            const bool holds = source.rel == Relation::Eq ? value == source.rhs
                : source.rel == Relation::Neq ? value != source.rhs : value <= source.rhs;
            if (!holds) return std::nullopt;
        }
        return free;
    } catch (const ResourceExhausted&) {
        return std::nullopt;
    }
}

} // namespace xolver
