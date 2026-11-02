#include "algebra/linear/AffineIntegerDomain.h"

namespace xolver {
namespace {
bool holds(const mpq_class& value, Relation relation) {
    switch (relation) {
        case Relation::Eq: return value == 0;
        case Relation::Neq: return value != 0;
        case Relation::Lt: return value < 0;
        case Relation::Leq: return value <= 0;
        case Relation::Gt: return value > 0;
        case Relation::Geq: return value >= 0;
    }
    return false;
}
}

void AffineIntegerDomain::constrain(const mpq_class& coefficient,
                                    const mpq_class& constant, Relation relation) {
    if (inconsistent_) return;
    if (coefficient == 0) {
        inconsistent_ = !holds(constant, relation);
        return;
    }
    const mpq_class boundary = -constant / coefficient;
    if (coefficient < 0) {
        switch (relation) {
            case Relation::Lt: relation = Relation::Gt; break;
            case Relation::Leq: relation = Relation::Geq; break;
            case Relation::Gt: relation = Relation::Lt; break;
            case Relation::Geq: relation = Relation::Leq; break;
            default: break;
        }
    }
    mpz_class floor, ceil;
    mpz_fdiv_q(floor.get_mpz_t(), boundary.get_num_mpz_t(), boundary.get_den_mpz_t());
    mpz_cdiv_q(ceil.get_mpz_t(), boundary.get_num_mpz_t(), boundary.get_den_mpz_t());
    const auto lower = [&](const mpz_class& value) {
        if (!lower_ || value > *lower_) lower_ = value;
    };
    const auto upper = [&](const mpz_class& value) {
        if (!upper_ || value < *upper_) upper_ = value;
    };
    switch (relation) {
        case Relation::Eq:
            if (floor != ceil) inconsistent_ = true;
            else { lower(floor); upper(floor); }
            break;
        case Relation::Neq:
            if (floor == ceil) excluded_.insert(floor);
            break;
        case Relation::Lt: upper(ceil - 1); break;
        case Relation::Leq: upper(floor); break;
        case Relation::Gt: lower(floor + 1); break;
        case Relation::Geq: lower(ceil); break;
    }
    if (lower_ && upper_ && *lower_ > *upper_) inconsistent_ = true;
}

std::optional<mpz_class> AffineIntegerDomain::leastAtLeast(const mpz_class& minimum) const {
    if (inconsistent_) return std::nullopt;
    mpz_class value = lower_ && *lower_ > minimum ? *lower_ : minimum;
    while (excluded_.contains(value)) ++value;
    if (upper_ && value > *upper_) return std::nullopt;
    return value;
}

} // namespace xolver
