#pragma once

#include <gmpxx.h>
#include <optional>

namespace xolver {

struct EuclideanDivision {
    mpz_class quotient;
    mpz_class remainder;
};

// The unique decomposition n = d*q + r with 0 <= r < |d|.
// Zero division has no arithmetic value; its interpretation belongs to the caller.
inline std::optional<EuclideanDivision> euclideanDivMod(
    const mpz_class& numerator, const mpz_class& divisor) {
    if (divisor == 0) return std::nullopt;
    const mpz_class magnitude = abs(divisor);
    EuclideanDivision result;
    mpz_fdiv_qr(result.quotient.get_mpz_t(), result.remainder.get_mpz_t(),
                numerator.get_mpz_t(), magnitude.get_mpz_t());
    if (divisor < 0) result.quotient = -result.quotient;
    return result;
}

} // namespace xolver
