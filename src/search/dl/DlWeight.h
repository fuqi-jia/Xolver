#pragma once

#include <gmpxx.h>
#include <string>

namespace xolver {

// ============================================================================
// IDL weight: plain integer (GMP mpz_class)
// ============================================================================
using IdlWeight = mpz_class;

// ============================================================================
// RDL weight: rational + infinitesimal delta coefficient.
// Interpreted as c + deltaCoeff * δ, where δ > 0 is infinitesimal.
// ============================================================================
struct RdlWeight {
    mpq_class c;      // rational part
    int deltaCoeff;   // usually 0 or -1

    RdlWeight() : c(0), deltaCoeff(0) {}
    RdlWeight(const mpq_class& c_, int d = 0) : c(c_), deltaCoeff(d) {}

    bool isNegative() const {
        return c < 0 || (c == 0 && deltaCoeff < 0);
    }

    bool isZero() const {
        return c == 0 && deltaCoeff == 0;
    }
};

inline bool operator<(const RdlWeight& a, const RdlWeight& b) {
    if (a.c != b.c) return a.c < b.c;
    return a.deltaCoeff < b.deltaCoeff;
}

inline bool operator>(const RdlWeight& a, const RdlWeight& b) {
    return b < a;
}

inline bool operator==(const RdlWeight& a, const RdlWeight& b) {
    return a.c == b.c && a.deltaCoeff == b.deltaCoeff;
}

inline bool operator!=(const RdlWeight& a, const RdlWeight& b) {
    return !(a == b);
}

inline bool operator<=(const RdlWeight& a, const RdlWeight& b) {
    return !(b < a);
}

inline bool operator>=(const RdlWeight& a, const RdlWeight& b) {
    return !(a < b);
}

inline RdlWeight operator+(const RdlWeight& a, const RdlWeight& b) {
    return RdlWeight(a.c + b.c, a.deltaCoeff + b.deltaCoeff);
}

inline RdlWeight operator-(const RdlWeight& a, const RdlWeight& b) {
    return RdlWeight(a.c - b.c, a.deltaCoeff - b.deltaCoeff);
}

inline RdlWeight operator-(const RdlWeight& a) {
    return RdlWeight(-a.c, -a.deltaCoeff);
}

} // namespace xolver
