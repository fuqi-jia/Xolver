#pragma once

#include "ir/types.h"
#include <gmpxx.h>
#include <optional>
#include <set>

namespace xolver {

// Exact domain of one integer under rational affine constraints. Independent
// of SAT literals, arithmetic solvers and candidate-generation policy.
class AffineIntegerDomain {
public:
    void constrain(const mpq_class& coefficient, const mpq_class& constant,
                   Relation relation);
    std::optional<mpz_class> leastAtLeast(const mpz_class& minimum) const;
    const std::optional<mpz_class>& lowerBound() const { return lower_; }
    const std::optional<mpz_class>& upperBound() const { return upper_; }

private:
    std::optional<mpz_class> lower_, upper_;
    std::set<mpz_class> excluded_;
    bool inconsistent_ = false;
};

} // namespace xolver
