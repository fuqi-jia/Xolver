#pragma once

#include <concepts>
#include <gmpxx.h>
#include <string>

namespace xolver {

/**
 * @brief Delta-rational: Q_δ = { a + b·δ | a,b ∈ Q }
 *
 * Used to handle strict inequalities exactly in General Simplex.
 * δ is a positive infinitesimal.
 *
 * Comparison: a+bδ < c+dδ  iff  a < c  or  (a == c and b < d)
 *
 * Examples:
 *   x > 3   →   lower bound = 3 + 1·δ  = DeltaRational(3, 1)
 *   x < 5   →   upper bound = 5 - 1·δ  = DeltaRational(5, -1)
 *   x >= 2  →   lower bound = 2        = DeltaRational(2, 0)
 *   x <= 7  →   upper bound = 7        = DeltaRational(7, 0)
 */
struct DeltaRational {
    mpq_class a;  // real part
    mpq_class b;  // delta coefficient

    DeltaRational() : a(0), b(0) {}
    // Evaluate GMP expressions directly into the owned components. Const
    // operands retain the borrowing semantics of rational inputs, including
    // rvalues; no expression object or operand reference escapes construction.
    template<typename A = mpq_class>
        requires std::constructible_from<mpq_class, const A&>
    explicit DeltaRational(const A& _a) : a(_a), b(0) {}
    template<typename A = mpq_class, typename B = mpq_class>
        requires (std::constructible_from<mpq_class, const A&> &&
                  std::constructible_from<mpq_class, const B&>)
    DeltaRational(const A& _a, const B& _b) : a(_a), b(_b) {}

    bool isZero() const { return a == 0 && b == 0; }
    bool isNonZero() const { return a != 0 || b != 0; }

    bool operator<(const DeltaRational& rhs) const {
        if (a != rhs.a) return a < rhs.a;
        return b < rhs.b;
    }
    bool operator>(const DeltaRational& rhs) const {
        if (a != rhs.a) return a > rhs.a;
        return b > rhs.b;
    }
    bool operator==(const DeltaRational& rhs) const {
        return a == rhs.a && b == rhs.b;
    }
    bool operator!=(const DeltaRational& rhs) const {
        return !(*this == rhs);
    }
    bool operator<=(const DeltaRational& rhs) const {
        return !(rhs < *this);
    }
    bool operator>=(const DeltaRational& rhs) const {
        return !(*this < rhs);
    }

    DeltaRational operator+(const DeltaRational& rhs) const {
        return DeltaRational(a + rhs.a, b + rhs.b);
    }
    DeltaRational operator-(const DeltaRational& rhs) const {
        return DeltaRational(a - rhs.a, b - rhs.b);
    }
    DeltaRational operator-() const {
        return DeltaRational(-a, -b);
    }
    DeltaRational operator*(const mpq_class& c) const {
        return DeltaRational(a * c, b * c);
    }
    DeltaRational operator/(const mpq_class& c) const {
        return DeltaRational(a / c, b / c);
    }

    DeltaRational& operator+=(const DeltaRational& rhs) {
        a += rhs.a; b += rhs.b; return *this;
    }
    DeltaRational& operator-=(const DeltaRational& rhs) {
        a -= rhs.a; b -= rhs.b; return *this;
    }

    std::string toString() const {
        if (b == 0) return a.get_str();
        std::string s = a.get_str();
        if (b > 0) s += " + " + b.get_str() + "δ";
        else       s += " - " + mpq_class(-b).get_str() + "δ";
        return s;
    }
};

// Convenience: treat mpq_class as DeltaRational in mixed ops
inline DeltaRational operator+(const mpq_class& c, const DeltaRational& d) {
    return DeltaRational(c + d.a, d.b);
}
inline DeltaRational operator-(const mpq_class& c, const DeltaRational& d) {
    return DeltaRational(c - d.a, -d.b);
}
inline DeltaRational operator*(const mpq_class& c, const DeltaRational& d) {
    return DeltaRational(c * d.a, c * d.b);
}

} // namespace xolver
