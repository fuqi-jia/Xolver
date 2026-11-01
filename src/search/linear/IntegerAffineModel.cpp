#include "search/linear/IntegerAffineModel.h"
#include "search/presolve/IntegerLinearAlgebra.h"

#include <algorithm>
#include <map>
#include <set>
#include <limits>

namespace xolver {

std::optional<IntegerRadixDecomposition> findIntegerRadixDecomposition(
    const NormalizedConstraint& equation, const IntegerBoundsLookup& bounds) {
    if (equation.rel != Relation::Eq || equation.rhs.get_den() != 1) return std::nullopt;
    std::map<std::string, mpz_class> terms;
    for (const auto& [name, coefficient] : equation.lhs.terms) {
        if (coefficient.get_den() != 1) return std::nullopt;
        terms[name] += coefficient.get_num();
        if (terms[name] == 0) terms.erase(name);
    }
    if (terms.size() != 3) return std::nullopt;
    mpz_class divisor = 0, rhs = equation.rhs.get_num();
    for (const auto& [name, coefficient] : terms) {
        (void)name;
        mpz_gcd(divisor.get_mpz_t(), divisor.get_mpz_t(), coefficient.get_mpz_t());
    }
    if (rhs % divisor != 0) return std::nullopt;
    rhs /= divisor;
    for (auto& [name, coefficient] : terms) { (void)name; coefficient /= divisor; }
    auto quotient = terms.end();
    for (auto it = terms.begin(); it != terms.end(); ++it) {
        if (it->second == 1 || it->second == -1) continue;
        if (quotient != terms.end()) return std::nullopt;
        quotient = it;
    }
    if (quotient == terms.end()) return std::nullopt;
    const mpz_class magnitude = abs(quotient->second);
    if (mpz_popcount(magnitude.get_mpz_t()) != 1) return std::nullopt;
    const auto exponent = mpz_scan1(magnitude.get_mpz_t(), 0);
    if (exponent > std::numeric_limits<unsigned>::max()) return std::nullopt;
    for (const auto& [remainder, coefficient] : terms) {
        if (remainder == quotient->first) continue;
        const auto range = bounds(remainder);
        if (!range || range->first < 0 || range->first > range->second || range->second >= magnitude)
            continue;
        for (const auto& [dividend, unit] : terms) {
            if (dividend == quotient->first || dividend == remainder || coefficient != -unit) continue;
            return IntegerRadixDecomposition{dividend, quotient->first, remainder,
                mpz_class(-rhs / unit), static_cast<unsigned>(exponent),
                (quotient->second > 0) == (unit > 0), range->first, range->second};
        }
    }
    return std::nullopt;
}

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

} // namespace xolver
