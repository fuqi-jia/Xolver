#pragma once

#include "theory/arith/interval/IntervalTypes.h"
#include <algorithm>
#include <cassert>

namespace xolver {

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
            // 0 in [lo, hi]: minimum is 0, maximum is max(lo^2, hi^2)
            mpz_class lo2 = a.lo * a.lo;
            mpz_class hi2 = a.hi * a.hi;
            return {mpz_class(0), std::max(lo2, hi2)};
        } else {
            // 0 not in [lo, hi]: minimum is min(lo^2, hi^2)
            mpz_class lo2 = a.lo * a.lo;
            mpz_class hi2 = a.hi * a.hi;
            return {std::min(lo2, hi2), std::max(lo2, hi2)};
        }
    } else {
        // Odd power: monotonic
        mpz_class loK = a.lo;
        mpz_class hiK = a.hi;
        for (uint32_t i = 1; i < k; ++i) {
            loK *= a.lo;
            hiK *= a.hi;
        }
        return {loK, hiK};
    }
}

} // namespace xolver
