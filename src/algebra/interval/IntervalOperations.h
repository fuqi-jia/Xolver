#pragma once

#include "algebra/interval/IntervalTypes.h"
#include <algorithm>
#include <cassert>

namespace xolver {

namespace interval_detail {
template <class T> T power(T base, uint32_t exponent) {
    T result(1);
    while (exponent) {
        if (exponent & 1)
            result *= base;
        exponent >>= 1;
        if (exponent)
            base *= base;
    }
    return result;
}
} // namespace interval_detail

inline IntervalZ intervalAdd(const IntervalZ& a, const IntervalZ& b) {
    return {a.lo + b.lo, a.hi + b.hi};
}

inline IntervalZ intervalSub(const IntervalZ& a, const IntervalZ& b) {
    return {a.lo - b.hi, a.hi - b.lo};
}

inline IntervalZ intervalNeg(const IntervalZ& a) {
    return {-a.hi, -a.lo};
}

inline IntervalZ intervalMul(const IntervalZ& a, const IntervalZ& b) {
    mpz_class ac = a.lo * b.lo;
    mpz_class ad = a.lo * b.hi;
    mpz_class bc = a.hi * b.lo;
    mpz_class bd = a.hi * b.hi;
    mpz_class lo = std::min({ac, ad, bc, bd});
    mpz_class hi = std::max({ac, ad, bc, bd});
    return {lo, hi};
}

inline IntervalZ intervalPow(const IntervalZ& a, uint32_t k) {
    if (k == 0) return {mpz_class(1), mpz_class(1)};
    if (k == 1) return a;

    if (k % 2 == 0) {
        // Even power
        if (a.containsZero()) {
            // 0 in [lo, hi]: minimum is 0, maximum is max(lo^k, hi^k)
            mpz_class loPower = interval_detail::power(a.lo, k);
            mpz_class hiPower = interval_detail::power(a.hi, k);
            return {mpz_class(0), std::max(loPower, hiPower)};
        } else {
            // 0 not in [lo, hi]: minimum is min(lo^k, hi^k)
            mpz_class loPower = interval_detail::power(a.lo, k);
            mpz_class hiPower = interval_detail::power(a.hi, k);
            return {std::min(loPower, hiPower), std::max(loPower, hiPower)};
        }
    } else {
        // Odd power: monotonic
        mpz_class loK = interval_detail::power(a.lo, k);
        mpz_class hiK = interval_detail::power(a.hi, k);
        return {loK, hiK};
    }
}

} // namespace xolver
