#pragma once
#include "base/WorkBudget.h"
#include <gmpxx.h>
namespace xolver::applications::smt::fp {
enum class Rounding { NearestEven, NearestAway, Positive, Negative, Zero };
enum class Arithmetic { Add, Subtract, Multiply, Divide };
// Exact IEEE binary arithmetic on concrete encodings. No host floating point.
mpz_class evaluate(Arithmetic, Rounding, std::size_t exponentBits, std::size_t significandBits,
                   const mpz_class &, const mpz_class &, WorkBudget &);
} // namespace xolver::applications::smt::fp
