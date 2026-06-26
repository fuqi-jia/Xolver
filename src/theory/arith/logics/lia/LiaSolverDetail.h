#pragma once
// Detail helpers extracted from LiaSolver.cpp so they can be shared across the
// split LiaSolver translation units (LiaSolver.cpp, LiaSolver_*.cpp). These were
// file-static free functions; promoting them to inline header functions keeps
// them header-shareable with identical (pure-function) behavior — every call
// site resolves to the same xolver:: name it did before the split.
#include <gmpxx.h>
#include "theory/core/TheoryAtomTypes.h"  // LinearAtomPayload

namespace xolver {

// True iff a linear atom payload is integral: integer rhs and all-integer
// coefficients on the lhs terms.
inline bool isIntegerLinearForm(const LinearAtomPayload& p) {
    if (!p.rhs.isRational() || p.rhs.asRational().get_den() != 1) return false;
    for (const auto& t : p.lhs.terms) {
        if (t.second.get_den() != 1) return false;
    }
    return true;
}

// Round a rational to the nearest integer (ties resolved by adding 1/2 then
// taking the floor).
inline mpz_class roundNearest(const mpq_class& q) {
    mpq_class h = q + mpq_class(1, 2);
    mpz_class r;
    mpz_fdiv_q(r.get_mpz_t(), h.get_num().get_mpz_t(), h.get_den().get_mpz_t());
    return r;
}

}  // namespace xolver
