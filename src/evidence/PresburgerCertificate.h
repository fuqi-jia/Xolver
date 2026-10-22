#pragma once

#include "ir/types.h"
#include <gmpxx.h>
#include <map>
#include <vector>

namespace xolver::proof {

// A canonical integer inequality: sum(coefficients[v] * v) <= bound.
// Premises must be tied to the original query by the proof consumer; these
// checkers establish arithmetic validity, not premise provenance.
struct IntegerInequality {
    std::map<VarId, mpz_class> coefficients;
    mpz_class bound;
};

// Nonnegative integer combination yields 0 <= a negative integer.
bool checkIntegerLinearContradiction(const std::vector<IntegerInequality>& premises,
                                     const std::vector<mpz_class>& multipliers);

// Divide coefficients by their gcd and round the upper bound toward -infinity.
bool checkIntegerGcdTightening(const IntegerInequality& premise,
                               const IntegerInequality& conclusion);

// For sum(a_i*x_i) = rhs, gcd(a_i) must divide rhs.
bool checkIntegerEqualityContradiction(const std::map<VarId, mpz_class>& coefficients,
                                       const mpz_class& rhs);

} // namespace xolver::proof
