#include "algebra/linear/IntegerIntervalCombination.h"
#include <stdexcept>
#include <utility>

namespace xolver {
namespace {
IntegerIntervalConflict combine(const BoundedIntegerForm& a,
                                const BoundedIntegerForm& b,
                                const mpz_class& left, const mpz_class& right) {
    IntegerIntervalConflict out;
    out.leftMultiplier = left;
    out.rightMultiplier = right;
    out.lower = left * (left >= 0 ? a.lower : a.upper) +
                right * (right >= 0 ? b.lower : b.upper);
    out.upper = left * (left >= 0 ? a.upper : a.lower) +
                right * (right >= 0 ? b.upper : b.lower);
    out.divisor = 0;
    for (std::size_t i = 0; i < a.coefficients.size(); ++i) {
        const mpz_class coefficient = left * a.coefficients[i] + right * b.coefficients[i];
        mpz_gcd(out.divisor.get_mpz_t(), out.divisor.get_mpz_t(), coefficient.get_mpz_t());
    }
    return out;
}

bool gap(const IntegerIntervalConflict& c) {
    if (c.divisor == 0) return c.lower > 0 || c.upper < 0;
    mpz_class first, last;
    mpz_cdiv_q(first.get_mpz_t(), c.lower.get_mpz_t(), c.divisor.get_mpz_t());
    mpz_fdiv_q(last.get_mpz_t(), c.upper.get_mpz_t(), c.divisor.get_mpz_t());
    return first > last;
}
} // namespace

bool verifyIntegerIntervalConflict(const BoundedIntegerForm& a,
                                  const BoundedIntegerForm& b,
                                  const IntegerIntervalConflict& certificate) {
    if (a.coefficients.size() != b.coefficients.size()) return false;
    const auto actual = combine(a, b, certificate.leftMultiplier, certificate.rightMultiplier);
    return actual.divisor == certificate.divisor && actual.lower == certificate.lower &&
           actual.upper == certificate.upper && gap(actual);
}

std::optional<IntegerIntervalConflict> findIntegerIntervalConflict(
    const BoundedIntegerForm& a, const BoundedIntegerForm& b, WorkBudget& budget) {
    if (a.coefficients.size() != b.coefficients.size())
        throw std::invalid_argument("integer interval coordinates differ");
    auto test = [&](const mpz_class& left, const mpz_class& right)
        -> std::optional<IntegerIntervalConflict> {
        budget.tick();
        auto candidate = combine(a, b, left, right);
        if (gap(candidate)) return candidate;
        return std::nullopt;
    };
    if (auto c = test(1, 0)) return c;
    if (auto c = test(0, 1)) return c;
    for (std::size_t i = 0; i < a.coefficients.size(); ++i) {
        // Also handles proportional forms: a coordinate-cancelling combination
        // becomes identically zero when the rows are linearly dependent.
        if (a.coefficients[i] != 0 || b.coefficients[i] != 0)
            if (auto c = test(b.coefficients[i], -a.coefficients[i])) return c;
        for (std::size_t j = i + 1; j < a.coefficients.size(); ++j) {
            budget.tick();
            const mpz_class determinant = a.coefficients[i] * b.coefficients[j] -
                                          a.coefficients[j] * b.coefficients[i];
            if (determinant == 0) continue;
            auto directions = [&](const std::vector<mpz_class>& row)
                -> std::optional<IntegerIntervalConflict> {
                auto direction = [&](const mpz_class& x, const mpz_class& y) {
                    const mpz_class left = b.coefficients[j] * x - b.coefficients[i] * y;
                    const mpz_class right = -a.coefficients[j] * x + a.coefficients[i] * y;
                    return test(left, right);
                };
                if (auto c = direction(1, 0)) return c;
                if (auto c = direction(0, 1)) return c;
                mpz_class numerator = abs(row[i]), denominator = abs(row[j]);
                mpz_class h0 = 0, h1 = 1, k0 = 1, k1 = 0;
                while (denominator != 0) {
                    mpz_class quotient, remainder;
                    mpz_fdiv_qr(quotient.get_mpz_t(), remainder.get_mpz_t(),
                                numerator.get_mpz_t(), denominator.get_mpz_t());
                    numerator = denominator;
                    denominator = std::move(remainder);
                    mpz_class h = quotient * h1 + h0, k = quotient * k1 + k0;
                    h0 = std::move(h1); h1 = std::move(h);
                    k0 = std::move(k1); k1 = std::move(k);
                    const mpz_class x = row[i] < 0 ? -h1 : h1;
                    const mpz_class y = row[j] < 0 ? -k1 : k1;
                    if (auto c = direction(x, y)) return c;
                }
                return std::nullopt;
            };
            if (auto c = directions(a.coefficients)) return c;
            if (auto c = directions(b.coefficients)) return c;
        }
    }
    return std::nullopt;
}
} // namespace xolver
