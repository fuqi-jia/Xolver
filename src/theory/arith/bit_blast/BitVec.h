#pragma once

#include "sat/SatSolver.h"
#include <gmpxx.h>
#include <vector>

namespace xolver::bitblast {

// Two's-complement bit-vector. bits[0] = LSB, bits.back() = MSB (sign bit,
// weight -2^(width-1)). Each bit is a SatLit in the owning SAT instance.
struct BitVec {
    std::vector<SatLit> bits;
    bool      isConst   = false;
    mpz_class constValue = 0;     // valid iff isConst

    unsigned width() const { return static_cast<unsigned>(bits.size()); }
    SatLit   sign()  const { return bits.back(); }
};

// A SatLit is satisfied iff the variable's value matches the literal polarity.
inline bool litValue(const SatSolver& sat, SatLit l) {
    return sat.value(l.var) == l.sign;
}

// Reconstruct the signed integer value of a solved bit-vector.
inline mpz_class readBitVec(const SatSolver& sat, const BitVec& bv) {
    mpz_class v = 0;
    unsigned w = bv.width();
    for (unsigned i = 0; i + 1 < w; ++i) {
        if (litValue(sat, bv.bits[i])) v += (mpz_class(1) << i);
    }
    if (w > 0 && litValue(sat, bv.bits[w - 1])) {
        v -= (mpz_class(1) << (w - 1));   // sign bit weight
    }
    return v;
}

} // namespace xolver::bitblast
