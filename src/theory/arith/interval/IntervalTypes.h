#pragma once

#include "theory/core/TheorySolver.h"
#include <gmpxx.h>
#include <vector>

namespace xolver {

/**
 * IntervalZ: integer interval [lo, hi] (inclusive).
 */
struct IntervalZ {
    mpz_class lo;
    mpz_class hi;

    bool isEmpty() const { return lo > hi; }
    bool contains(const mpz_class& v) const { return v >= lo && v <= hi; }
    bool containsZero() const { return lo <= 0 && hi >= 0; }
    mpz_class width() const { return hi - lo; }
};

/**
 * ReasonedInterval: an interval together with the SAT literals that justify it.
 */
struct ReasonedInterval {
    IntervalZ interval;
    std::vector<SatLit> reasons; // all SAT literals contributing to this bound
};

} // namespace xolver
