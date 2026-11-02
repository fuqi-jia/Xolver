#pragma once
#include "contracts/PresburgerFormula.h"
#include "algebra/linear/AffineIntegerDomain.h"
#include <optional>
#include <stdexcept>
#include <utility>

namespace xolver::pa::detail {
// Exact arithmetic kernel shared by numeric QE and free-model reconstruction.
// Charge owns work/deadline policy; no parser, SAT backend or finite search box
// is needed. A missing witness is an exact contradiction, unless Charge throws.
template<class Charge>
class UnaryArithmetic {
    Charge charge;
public:
    explicit UnaryArithmetic(Charge c) : charge(std::move(c)) {}
    // One congruence class; modulus is positive and 0 <= residue < modulus.
    struct Congruence {
        mpz_class residue = 0, modulus = 1;
        bool operator<(const Congruence& other) const {
            return std::tie(modulus, residue) < std::tie(other.modulus, other.residue);
        }
    };
    // Solve coefficient*x + constant == 0 (mod modulus). nullopt denotes
    // inconsistency, including a nonzero constant modulo a zero coefficient.
    std::optional<Congruence> congruence(const mpz_class& coefficient,
                                         const mpz_class& constant,
                                         const mpz_class& modulus) {
        charge(1 + mpz_size(coefficient.get_mpz_t()) + mpz_size(constant.get_mpz_t()) +
             mpz_size(modulus.get_mpz_t()));
        mpz_class gcd, inverse;
        mpz_gcdext(gcd.get_mpz_t(), inverse.get_mpz_t(), nullptr,
                   coefficient.get_mpz_t(), modulus.get_mpz_t());
        if (!mpz_divisible_p(constant.get_mpz_t(), gcd.get_mpz_t())) return {};
        Congruence result;
        result.modulus = modulus / gcd;
        result.residue = -(constant / gcd) * inverse;
        mpz_fdiv_r(result.residue.get_mpz_t(), result.residue.get_mpz_t(), result.modulus.get_mpz_t());
        return result;
    }
    // Generalized CRT, also valid for overlapping/non-coprime moduli.
    std::optional<Congruence> intersect(const Congruence& a, const Congruence& b) {
        const auto index = congruence(a.modulus, a.residue - b.residue, b.modulus);
        if (!index) return {};
        Congruence result;
        result.modulus = a.modulus * index->modulus;
        result.residue = a.residue + a.modulus * index->residue;
        mpz_fdiv_r(result.residue.get_mpz_t(), result.residue.get_mpz_t(), result.modulus.get_mpz_t());
        return result;
    }
    // After substituting the later projection values, inequalities give an
    // interval and positive divisibility gives one CRT progression. Negated
    // divisibility excludes progressions within it. Inclusion/exclusion counts
    // their complement exactly; binary search recovers a witness without a
    // numerical bound or a loop proportional to a modulus. Its exponential
    // dependence on the number of exclusions consumes the normal work budget.
    std::optional<mpz_class> solve(const Cube& cube, Var variable) {
        AffineIntegerDomain interval;
        Congruence positive;
        std::vector<Congruence> negative;
        for (const auto& literal : cube) {
            charge(1);
            mpz_class constant = literal.affine.constant;
            for (const auto& [v, coefficient] : literal.affine.coefficients)
                if (v != variable)
                    throw std::invalid_argument("PA unary arithmetic received another variable");
            const mpz_class coefficient = literal.affine.coefficient(variable);
            if (coefficient == 0) {
                const bool valid = literal.divisor == 0 ? constant <= 0 :
                    bool(mpz_divisible_p(constant.get_mpz_t(), literal.divisor.get_mpz_t())) !=
                        literal.negatedDivisibility;
                if (!valid) return {};
            } else if (literal.divisor != 0) {
                auto condition = congruence(coefficient, constant, literal.divisor);
                if (literal.negatedDivisibility) {
                    if (condition) negative.push_back(std::move(*condition));
                } else {
                    if (!condition) return {};
                    auto combined = intersect(positive, *condition);
                    if (!combined) return {};
                    positive = std::move(*combined);
                }
            } else {
                interval.constrain(mpq_class(coefficient), mpq_class(constant), Relation::Leq);
            }
        }
        const auto& lower = interval.lowerBound();
        const auto& upper = interval.upperBound();
        if (lower && upper && *lower > *upper) return {};
        std::optional<mpz_class> first, last;
        if (lower) {
            mpz_class difference = *lower - positive.residue;
            first.emplace();
            mpz_cdiv_q(first->get_mpz_t(), difference.get_mpz_t(), positive.modulus.get_mpz_t());
        }
        if (upper) {
            mpz_class difference = *upper - positive.residue;
            last.emplace();
            mpz_fdiv_q(last->get_mpz_t(), difference.get_mpz_t(), positive.modulus.get_mpz_t());
        }
        if (first && last && *first > *last) return {};
        std::set<Congruence> exclusions;
        mpz_class period = 1;
        for (const auto& condition : negative) {
            auto excluded = congruence(positive.modulus, positive.residue - condition.residue,
                                       condition.modulus);
            if (!excluded) continue; // disjoint from the positive CRT progression
            if (excluded->modulus == 1) return {};
            exclusions.insert(*excluded);
            mpz_lcm(period.get_mpz_t(), period.get_mpz_t(), excluded->modulus.get_mpz_t());
        }
        // Integer coefficients of characteristic functions for the allowed
        // indices: start with all integers, multiply by (1 - excluded) for each
        // forbidden progression, and coalesce equal intersections exactly.
        std::map<Congruence, mpz_class> counts{{Congruence{}, 1}};
        for (const auto& excluded : exclusions) {
            std::map<Congruence, mpz_class> change;
            for (const auto& [term, coefficient] : counts) {
                if (auto overlap = intersect(term, excluded)) {
                    charge(1 + mpz_size(coefficient.get_mpz_t()));
                    change[*overlap] -= coefficient;
                }
            }
            for (const auto& [term, coefficient] : change) {
                charge(1);
                auto [it, fresh] = counts.try_emplace(term, 0);
                it->second += coefficient;
                if (it->second == 0) counts.erase(it);
            }
            if (counts.empty()) return {};
        }
        mpz_class left = first ? *first : last ? mpz_class(*last - period + 1) : mpz_class(0);
        mpz_class right = left + period - 1;
        if (last && *last < right) right = *last;
        auto count = [&](const mpz_class& begin, const mpz_class& end) {
            mpz_class total = 0;
            for (const auto& [term, coefficient] : counts) {
                charge(1 + mpz_size(begin.get_mpz_t()) + mpz_size(end.get_mpz_t()) +
                     mpz_size(term.modulus.get_mpz_t()) + mpz_size(coefficient.get_mpz_t()));
                mpz_class a = end - term.residue, b = begin - 1 - term.residue;
                mpz_fdiv_q(a.get_mpz_t(), a.get_mpz_t(), term.modulus.get_mpz_t());
                mpz_fdiv_q(b.get_mpz_t(), b.get_mpz_t(), term.modulus.get_mpz_t());
                total += coefficient * (a - b);
            }
            return total;
        };
        if (count(left, right) == 0) return {};
        while (left < right) {
            mpz_class middle = left + right;
            mpz_fdiv_q_2exp(middle.get_mpz_t(), middle.get_mpz_t(), 1);
            if (count(left, middle) > 0) right = std::move(middle);
            else left = middle + 1;
        }
        return mpz_class(positive.residue + positive.modulus * left);
    }
};
} // namespace xolver::pa::detail
