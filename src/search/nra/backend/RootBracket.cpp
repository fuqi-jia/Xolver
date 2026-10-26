#include "search/nra/backend/RootBracket.h"
#include <algorithm>
#include <bit>

namespace xolver::nra_backend {
namespace {
std::size_t bits(const mpz_class& value) {
    return value == 0 ? 0 : mpz_sizeinbase(value.get_mpz_t(), 2);
}
bool dyadic(const mpq_class& value) {
    return value.get_den() > 0 && mpz_popcount(value.get_den_mpz_t()) == 1;
}
}

std::optional<RootBracket> compactRootBracket(
    const std::vector<mpz_class>& coefficients, const mpq_class& lower,
    const mpq_class& upper, std::size_t bitBudget, WorkBudget& work) {
    if (coefficients.size() < 2 || lower > upper || bitBudget == 0) return std::nullopt;
    std::size_t coefficientBits = 0;
    for (const auto& coefficient : coefficients) {
        work.tick();
        coefficientBits = std::max(coefficientBits, bits(coefficient));
    }
    const auto degree = coefficients.size() - 1;
    const auto overhead = std::bit_width(coefficients.size()) + 2;
    if (overhead > bitBudget || coefficientBits > bitBudget - overhead) return std::nullopt;
    const auto available = bitBudget - overhead - coefficientBits;
    auto fits = [&](const mpq_class& point) {
        const auto pointBits = std::max(bits(point.get_num()), bits(point.get_den()));
        // Horner numerators/denominators need at most coefficientBits +
        // degree * pointBits + log2(number of terms) bits. Divide first to
        // avoid overflowing the forecast itself.
        return pointBits <= available / degree;
    };
    auto evaluate = [&](const mpq_class& point) {
        mpq_class value(coefficients.front());
        for (std::size_t i = 1; i < coefficients.size(); ++i) {
            work.tick();
            value = value * point + coefficients[i];
        }
        return value;
    };
    if (lower == upper) {
        if (dyadic(lower) && fits(lower) && evaluate(lower) == 0)
            return RootBracket{lower, upper};
        return std::nullopt;
    }
    if (coefficients.back() == 0 && lower < 0 && upper > 0)
        return RootBracket{mpq_class(0), mpq_class(0)};
    if (dyadic(lower) && dyadic(upper) && fits(lower) && fits(upper))
        return RootBracket{lower, upper};

    // Round INWARD: the old interval certifies uniqueness, so a sign-changing
    // subinterval certifies the same root without another root-isolation pass.
    // Start with integers and increase dyadic precision only when necessary.
    const auto maxPrecision = available / degree == 0 ? 0 : available / degree - 1;
    for (std::size_t precision = 0;;) {
        work.tick();
        mpz_class denominator(1);
        mpz_mul_2exp(denominator.get_mpz_t(), denominator.get_mpz_t(), precision);
        mpq_class scaledLower = lower * denominator, scaledUpper = upper * denominator;
        mpz_class low, high;
        mpz_cdiv_q(low.get_mpz_t(), scaledLower.get_num_mpz_t(), scaledLower.get_den_mpz_t());
        mpz_fdiv_q(high.get_mpz_t(), scaledUpper.get_num_mpz_t(), scaledUpper.get_den_mpz_t());
        if (low <= high) {
            mpq_class lo(low, denominator), hi(high, denominator);
            lo.canonicalize(); hi.canonicalize();
            if (!fits(lo) || !fits(hi)) return std::nullopt;
            const auto flo = evaluate(lo);
            if (flo == 0 && lower < lo && lo < upper) return RootBracket{lo, lo};
            if (lo != hi) {
                const auto fhi = evaluate(hi);
                if (fhi == 0 && lower < hi && hi < upper) return RootBracket{hi, hi};
                if (flo != 0 && fhi != 0 && sgn(flo) != sgn(fhi))
                    return RootBracket{std::move(lo), std::move(hi)};
            }
        }
        if (precision == maxPrecision) break;
        precision = precision == 0 ? 1 :
            (precision > maxPrecision / 2 ? maxPrecision : precision * 2);
    }
    return std::nullopt;
}
} // namespace xolver::nra_backend
