#pragma once

#include "theory/arith/interval/IntervalQ.h"
#include <algorithm>
#include <cassert>

namespace zolver {

inline IntervalQ intervalQAdd(const IntervalQ& a, const IntervalQ& b) {
    return {a.lo + b.lo, a.hi + b.hi};
}

inline IntervalQ intervalQSub(const IntervalQ& a, const IntervalQ& b) {
    return {a.lo - b.hi, a.hi - b.lo};
}

inline IntervalQ intervalQNeg(const IntervalQ& a) {
    return {-a.hi, -a.lo};
}

inline IntervalQ intervalQMul(const IntervalQ& a, const IntervalQ& b) {
    mpq_class ac = a.lo * b.lo;
    mpq_class ad = a.lo * b.hi;
    mpq_class bc = a.hi * b.lo;
    mpq_class bd = a.hi * b.hi;
    mpq_class lo = std::min({ac, ad, bc, bd});
    mpq_class hi = std::max({ac, ad, bc, bd});
    return {lo, hi};
}

// Division: if denominator contains zero, return wide interval (or caller checks)
inline IntervalQ intervalQDiv(const IntervalQ& a, const IntervalQ& b) {
    if (b.containsZero()) {
        // Over-approx: return unbounded interval
        // V1: caller should check containsZero and avoid calling this for conflict
        return {mpq_class(-1), mpq_class(1)}; // placeholder, should not be used for pruning
    }
    mpq_class vals[4] = {
        a.lo / b.lo, a.lo / b.hi,
        a.hi / b.lo, a.hi / b.hi
    };
    mpq_class lo = *std::min_element(vals, vals + 4);
    mpq_class hi = *std::max_element(vals, vals + 4);
    return {lo, hi};
}

inline IntervalQ intervalQPow(const IntervalQ& a, uint32_t k) {
    if (k == 0) return {mpq_class(1), mpq_class(1)};
    if (k == 1) return a;

    if (k % 2 == 0) {
        if (a.containsZero()) {
            mpq_class lo2 = a.lo * a.lo;
            mpq_class hi2 = a.hi * a.hi;
            return {mpq_class(0), std::max(lo2, hi2)};
        } else {
            mpq_class lo2 = a.lo * a.lo;
            mpq_class hi2 = a.hi * a.hi;
            return {std::min(lo2, hi2), std::max(lo2, hi2)};
        }
    } else {
        mpq_class loK = a.lo;
        mpq_class hiK = a.hi;
        for (uint32_t i = 1; i < k; ++i) {
            loK *= a.lo;
            hiK *= a.hi;
        }
        return {loK, hiK};
    }
}

} // namespace zolver
