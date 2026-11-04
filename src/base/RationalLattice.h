#pragma once

#include "base/WorkBudget.h"
#include <gmpxx.h>
#include <optional>

namespace xolver {

// Rational coefficients of integral terms place every sum on this lattice.
// Include the constant term. Domain membership and accounting are caller-owned;
// the term range may come from the solver or an independent certificate reader.
template<class Terms, class IsInteger, class Tick>
std::optional<mpq_class> rationalLatticeStep(
    const Terms& terms, IsInteger isInteger, Tick tick) {
    mpz_class numerator = 0, denominator = 1;
    for (const auto& [monomial, coefficient] : terms) {
        tick(1 + monomial.size());
        for (const auto& [variable, exponent] : monomial) {
            (void)exponent;
            if (!isInteger(variable)) return std::nullopt;
        }
        tick(mpz_sizeinbase(coefficient.get_num_mpz_t(), 2) +
             mpz_sizeinbase(coefficient.get_den_mpz_t(), 2));
        mpz_gcd(numerator.get_mpz_t(), numerator.get_mpz_t(), coefficient.get_num_mpz_t());
        mpz_lcm(denominator.get_mpz_t(), denominator.get_mpz_t(), coefficient.get_den_mpz_t());
        if (mpz_sizeinbase(denominator.get_mpz_t(), 2) > 4096)
            throw ResourceExhausted("integer polynomial lattice allocation exhausted");
    }
    if (numerator == 0) return std::nullopt;
    return mpq_class(numerator, denominator);
}

} // namespace xolver
