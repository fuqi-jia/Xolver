#pragma once

// RealValue — a single canonical representation for Real-sorted values,
// unifying Zolver's two parallel numeric types (rational `mpq_class` and the
// CDCAC algebraic `RealAlg`).  Modeled on cvc5's RealAlgebraicNumber: a value is
// either an exact rational or a real algebraic number (defining polynomial +
// isolation interval).  Rational⊕Rational stays Rational; an Algebraic operand
// promotes the result to Algebraic.
//
// Location is `src/util/` (not `theory/arith/nra/`) so it is reachable from
// expr/, theory/, util/, and the public API without pulling in libpoly headers.
//
// PHASE 0 STATUS: this is the interface skeleton.  Every method body is a stub
// that throws std::logic_error("RealValue: not implemented") (see
// RealValue.cpp).  Phase 1 implements the bodies (libpoly delegation for the
// algebraic case) and the accompanying tests flip from skipped→passing.

#include <cstdint>
#include <gmpxx.h>
#include <optional>
#include <string>
#include <string_view>
#include <variant>
#include <vector>

namespace zolver {

// A real algebraic number: a real root of `defining polynomial`, pinned by an
// isolation interval that contains exactly that one root.  Owns its own integer
// coefficients so the value is safe to copy across solver boundaries (it does
// NOT borrow any libpoly handle — see the note below).
//
// Canonical form (enforced at construction in Phase 1): integer coefficients,
// content GCD = 1, positive leading coefficient.  coefficients[i] is the
// coefficient of x^i.
//
// NOTE (Phase-0 design decision): the predecessor plan proposed a
// `void* libpolyHandle` cache field here.  It is intentionally OMITTED — a raw
// non-owning pointer inside a value type advertised as "safe to copy" is a
// double-free / dangling hazard the moment a copy outlives the original handle.
// If profiling in Phase 1/2 shows the resultant/comparison cost dominates, add
// a `std::shared_ptr<void>` (with a libpoly deleter) that is explicitly excluded
// from equality and hashing — never a raw `void*`.
struct AlgebraicNumber {
    std::vector<mpz_class> coefficients;  // coefficients[i] = coeff of x^i
    mpq_class lower;                       // isolation interval [lower, upper]
    mpq_class upper;
    bool lowerOpen = true;
    bool upperOpen = true;
};

// A single Real value: exact rational, or real algebraic.
class RealValue {
public:
    enum class Kind : uint8_t { Rational, Algebraic };

    RealValue();  // defaults to Rational 0

    // -- Construction (explicit only; no implicit int promotion) --------------
    static RealValue fromInt(int64_t v);
    static RealValue fromMpz(const mpz_class& v);
    static RealValue fromMpq(mpq_class q);          // by value
    static RealValue fromAlgebraic(AlgebraicNumber a);
    // Parse a canonical SMT-LIB integer-or-rational literal ("3", "(/ 3 4)",
    // "(- (/ 3 4))", "3/4").  Throws std::invalid_argument on bad input.
    static RealValue parse(std::string_view s);

    // -- Kind queries ---------------------------------------------------------
    Kind kind() const;                              // derived from storage_
    bool isRational() const;
    bool isAlgebraic() const;

    // -- Accessors ------------------------------------------------------------
    // asRational() asserts isRational(); prefer tryAsRational() when conditional.
    const mpq_class& asRational() const;
    std::optional<mpq_class> tryAsRational() const;
    const AlgebraicNumber& asAlgebraic() const;

    // -- Arithmetic (Algebraic in either operand promotes the result) ---------
    RealValue operator+(const RealValue& other) const;
    RealValue operator-(const RealValue& other) const;
    RealValue operator*(const RealValue& other) const;
    RealValue operator/(const RealValue& other) const;   // throws on /0
    RealValue operator-() const;

    // -- Comparison (total order on R; -1/0/+1) -------------------------------
    // May refine an algebraic isolation interval (deterministic result).
    int compare(const RealValue& other) const;
    bool operator<(const RealValue& o) const { return compare(o) < 0; }
    bool operator<=(const RealValue& o) const { return compare(o) <= 0; }
    bool operator==(const RealValue& o) const { return compare(o) == 0; }
    bool operator!=(const RealValue& o) const { return compare(o) != 0; }
    bool operator>(const RealValue& o) const { return compare(o) > 0; }
    bool operator>=(const RealValue& o) const { return compare(o) >= 0; }

    int sign() const;                                // -1, 0, +1
    bool isZero() const { return sign() == 0; }

    // -- Integer predicates ---------------------------------------------------
    bool isExactInteger() const;
    mpz_class floor() const;
    mpz_class ceil() const;

    // -- Serialization --------------------------------------------------------
    // toSmtLib2(): rationals → internal integer form "n" / "(/ n d)" / "(- ...)"
    //   (parseable by parse()).  Algebraics → the SMT-COMP 2026 Model-Validation
    //   form (root-of-with-interval (coeffs c0..cn) min max) with Real-sort model
    //   values for the interval; a rational-singleton algebraic falls back to a
    //   Real-sort model value ("5.0").
    // toDebugString(): always defined, never throws; for logs/diagnostics.
    std::string toSmtLib2() const;
    std::string toDebugString() const;

private:
    // The variant is the single source of truth for the kind (index 0 ==
    // Rational, 1 == Algebraic); no separate tag field is stored.
    std::variant<mpq_class, AlgebraicNumber> storage_;
};

// RealValue ∪ {-∞, +∞} — for IntervalSet endpoints and tableau bounds.  The
// open/closed bit lives on the consuming Interval, NOT on the value itself.
class ExtendedRealValue {
public:
    enum class Kind : uint8_t { NegInf, Finite, PosInf };

    ExtendedRealValue();  // defaults to Finite 0
    static ExtendedRealValue negInf();
    static ExtendedRealValue posInf();
    static ExtendedRealValue finite(RealValue v);

    Kind kind() const;
    bool isFinite() const;
    bool isNegInf() const;
    bool isPosInf() const;
    const RealValue& asFinite() const;              // asserts isFinite()

    int compare(const ExtendedRealValue& other) const;
    bool operator<(const ExtendedRealValue& o) const { return compare(o) < 0; }
    bool operator<=(const ExtendedRealValue& o) const { return compare(o) <= 0; }
    bool operator==(const ExtendedRealValue& o) const { return compare(o) == 0; }
    bool operator!=(const ExtendedRealValue& o) const { return compare(o) != 0; }
    bool operator>(const ExtendedRealValue& o) const { return compare(o) > 0; }
    bool operator>=(const ExtendedRealValue& o) const { return compare(o) >= 0; }

private:
    Kind kind_ = Kind::Finite;
    RealValue finite_;
};

} // namespace zolver

namespace std {
// Hash consistent with RealValue::operator== (soundness invariant 5): equal
// values must hash equal, even across the Rational/Algebraic kind boundary
// (e.g. fromInt(5) == fromAlgebraic(root of x-5)).  Hashing on floor() is the
// uniform fingerprint that any two equal reals share regardless of
// representation.  Coarse (values in [n,n+1) collide) but provably sound;
// unordered containers resolve collisions via operator==.
template <>
struct hash<zolver::RealValue> {
    size_t operator()(const zolver::RealValue& v) const;
};
} // namespace std
