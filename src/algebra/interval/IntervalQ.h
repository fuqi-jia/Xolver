#pragma once

#include <gmpxx.h>

namespace xolver {

/**
 * IntervalQ: rational interval [lo, hi] (inclusive, finite only in V1).
 */
struct IntervalQ {
    mpq_class lo;
    mpq_class hi;

    bool isEmpty() const { return lo > hi; }
    bool contains(const mpq_class& v) const { return v >= lo && v <= hi; }
    bool containsZero() const { return lo <= 0 && hi >= 0; }
    mpq_class width() const { return hi - lo; }
};

} // namespace xolver
