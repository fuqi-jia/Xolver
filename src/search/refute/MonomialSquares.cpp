#include "search/refute/MonomialSquares.h"
#include <algorithm>
#include <cstdint>
#include <map>

namespace xolver {
namespace {
bool splitPair(const MonomialKey& a, const MonomialKey& b,
               MonomialKey& center, MonomialSquare& square, WorkBudget& budget) {
    size_t i = 0, j = 0;
    while (i < a.size() || j < b.size()) {
        budget.tick();
        const auto variable = i == a.size() ? b[j].first :
            j == b.size() ? a[i].first : std::min(a[i].first, b[j].first);
        const int x = i < a.size() && a[i].first == variable ? a[i++].second : 0;
        const int y = j < b.size() && b[j].first == variable ? b[j++].second : 0;
        const int64_t sum = int64_t(x) + y;
        if (sum % 2) return false;
        if (sum) center.emplace_back(variable, static_cast<int>(sum / 2));
        const int common = std::min(x, y);
        if (common) square.weight.emplace_back(variable, common);
        if (x > common) square.left.emplace_back(variable, (x - common) / 2);
        if (y > common) square.right.emplace_back(variable, (y - common) / 2);
    }
    return true;
}
}

MonomialSquareDecomposition decomposeMonomialSquares(
    const RationalPolynomial& polynomial,
    const std::function<bool(const MonomialKey&)>& nonnegative,
    WorkBudget& budget) {
    std::map<MonomialKey, mpq_class> coefficients;
    std::vector<MonomialKey> positive;
    bool hasNegative = false;
    auto normalized = polynomial;
    normalized.normalize();
    for (const auto& [monomial, coefficient] : normalized.terms()) {
        budget.tick();
        coefficients.emplace(monomial, coefficient);
        if (coefficient > 0) positive.push_back(monomial);
        hasNegative |= coefficient < 0;
    }
    MonomialSquareDecomposition result;
    if (hasNegative && nonnegative) {
        // Endpoints only lose positive mass and negative centers only move
        // toward zero. A single traversal therefore visits every usable pair.
        for (size_t i = 0; i < positive.size(); ++i) {
            for (size_t j = i + 1; j < positive.size(); ++j) {
                budget.tick();
                auto& a = coefficients.at(positive[i]);
                auto& b = coefficients.at(positive[j]);
                if (a <= 0 || b <= 0) continue;
                MonomialKey center;
                MonomialSquare square;
                if (!splitPair(positive[i], positive[j], center, square, budget)) continue;
                auto found = coefficients.find(center);
                if (found == coefficients.end() || found->second >= 0 || !nonnegative(square.weight)) continue;
                const mpq_class needed = -found->second / 2;
                const mpq_class amount = std::min(needed, std::min(a, b));
                a -= amount;
                b -= amount;
                found->second += 2 * amount;
                square.coefficient = amount;
                result.squares.push_back(std::move(square));
            }
        }
    }
    for (const auto& [monomial, coefficient] : coefficients)
        if (coefficient != 0) result.remainder.addTerm(monomial, coefficient);
    result.remainder.normalize();
    return result;
}

std::optional<MonomialEquationReduction> reduceByMonomialEquation(
    const RationalPolynomial& polynomial, const RationalPolynomial& equation,
    VarId variable, WorkBudget& budget) {
    if (equation.degree(variable) != 1 || polynomial.degree(variable) < 1) return std::nullopt;
    const auto leading = equation.leadingCoefficient(variable);
    if (leading.terms().size() != 1) return std::nullopt;
    const auto& [divisor, scale] = *leading.terms().begin();
    MonomialEquationReduction result{{}, polynomial};
    for (int degree = result.remainder.degree(variable); degree >= 1;) {
        budget.tick(result.remainder.terms().size() + 1);
        const auto coefficient = result.remainder.leadingCoefficient(variable);
        RationalPolynomial term;
        for (const auto& [monomial, value] : coefficient.terms()) {
            budget.tick(monomial.size() + divisor.size() + 1);
            auto powers = monomial;
            for (const auto& [var, exponent] : divisor) {
                const auto found = std::find_if(powers.begin(), powers.end(),
                    [&](const auto& power) { return power.first == var; });
                if (found == powers.end() || found->second < exponent) return std::nullopt;
                found->second -= exponent;
            }
            MonomialKey reduced;
            for (const auto& power : powers) if (power.second) reduced.push_back(power);
            term.addTerm(reduced, value / scale);
        }
        term.normalize();
        if (degree > 1) term = term * RationalPolynomial::fromVar(variable, degree - 1, 1);
        budget.tick(term.terms().size() * equation.terms().size() + 1);
        result.quotient += term;
        result.remainder -= term * equation;
        const int next = result.remainder.degree(variable);
        if (next >= degree) return std::nullopt;
        degree = next;
    }
    return result;
}

} // namespace xolver
