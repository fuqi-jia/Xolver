#pragma once

#include "expr/types.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include "theory/arith/poly/FlatMonomialMap.h"
#include <gmpxx.h>
#include <map>
#include <set>
#include <vector>
#include <optional>
#include <utility>

namespace zolver {

/**
 * Monomial key: sorted list of (varId, exponent) with exponents > 0.
 * Empty key represents the constant term.
 */
using MonomialKey = FlatMonomialMap<mpq_class>::Key;

/**
 * A multivariate polynomial with rational coefficients.
 *
 * Used as an intermediate representation before converting to
 * integer-coefficient libpoly polynomials.  All operations are exact
 * rational arithmetic (arbitrary precision).
 *
 * Invariant after normalize():
 *   - terms are sorted by MonomialKey (lexicographic on varId then exp)
 *   - zero coefficients are removed
 *   - each variable appears at most once in a monomial with positive exponent
 */
class RationalPolynomial {
public:
    RationalPolynomial() = default;

    // -- Construction helpers -------------------------------------------------

    static RationalPolynomial fromConstant(const mpq_class& c);
    static RationalPolynomial fromVar(VarId v, int exp, const mpq_class& coeff);

    void addTerm(const MonomialKey& key, const mpq_class& coeff);
    void addConstant(const mpq_class& coeff);
    void addVar(VarId v, int exp, const mpq_class& coeff);

    // -- Queries --------------------------------------------------------------

    bool isZero() const { return terms_.empty(); }
    bool isConstant() const;
    mpq_class constantValue() const;
    const FlatMonomialMap<mpq_class>& terms() const { return terms_; }

    // -- CDCAC V1 extensions --------------------------------------------------

    /** Does this polynomial contain the given variable? */
    bool contains(VarId v) const;

    /** Degree of this polynomial in the given variable. Returns -1 for zero poly. */
    int degree(VarId v) const;

    /**
     * Coefficients when viewing this polynomial as univariate in `v`.
     * Result[i] = coefficient of v^i (i from 0 to degree).
     * Each coefficient is a RationalPolynomial in the remaining variables.
     */
    std::vector<RationalPolynomial> coefficients(VarId v) const;

    /** Leading coefficient w.r.t. variable v. Returns zero polynomial if p is zero. */
    RationalPolynomial leadingCoefficient(VarId v) const;

    /** Partial derivative w.r.t. variable v. */
    RationalPolynomial derivative(VarId v) const;

    /** Pseudo-remainder of this polynomial divided by divisor, w.r.t. variable v. */
    RationalPolynomial pseudoRemainder(VarId v, const RationalPolynomial& divisor) const;

    /** Set of all variables appearing in this polynomial. */
    std::set<VarId> variables() const;

    /** Highest index of any variable in varOrder, or -1 if constant. */
    int highestVariableLevel(const std::vector<VarId>& varOrder) const;

    /** Substitute a rational value for a variable. */
    RationalPolynomial substituteRational(VarId v, const mpq_class& q) const;

    /**
     * Substitute a polynomial expression for a variable (exact).
     * Every occurrence of v^k in a monomial is replaced by expr^k, multiplied
     * by the rest of the monomial.  Result is normalized.  `expr` should not
     * contain v (the caller is responsible for acyclicity / transitive
     * elimination ordering).  Used by the NRA affine pre-elimination stage to
     * substitute `v = (linear RationalPolynomial)` out of constraint polys.
     */
    RationalPolynomial substitute(VarId v, const RationalPolynomial& expr) const;

    // -- V2-1: content and primitive part ------------------------------------

    /**
     * Content of this polynomial w.r.t. variable v.
     *
     * If all coefficients (viewed as univariate in v) are constants,
     * returns the GCD of those coefficients as a rational number.
     * If coefficients are multivariate polynomials, returns 1
     * (treated as primitive for V2-1; V2-4 multivariate GCD will refine).
     */
    mpq_class content(VarId v) const;

    /**
     * Primitive part w.r.t. variable v: p / content(v).
     * If content is 0 or 1, returns a copy of this polynomial.
     */
    RationalPolynomial primitivePart(VarId v) const;

    /** Convert back to PolyId in the given kernel. */
    PolyId toPolyId(PolynomialKernel& kernel) const;

    // -- Algebraic operations -------------------------------------------------

    RationalPolynomial operator+(const RationalPolynomial& other) const;
    RationalPolynomial operator-(const RationalPolynomial& other) const;
    RationalPolynomial operator*(const RationalPolynomial& other) const;
    RationalPolynomial operator-() const;
    RationalPolynomial& operator+=(const RationalPolynomial& other);
    RationalPolynomial& operator-=(const RationalPolynomial& other);
    RationalPolynomial& operator*=(const mpq_class& scalar);

    RationalPolynomial pow(uint32_t n) const;

    // -- Normalization --------------------------------------------------------

    /**
     * Merge like terms, delete zero coefficients, canonicalize variable order.
     * Must be called before toPrimitiveInteger() if terms were added manually.
     */
    void normalize();

    // -- Conversion to integer polynomial -------------------------------------

    /**
     * Convert to a primitive integer-coefficient polynomial.
     *
     * Computes:
     *   D = lcm of all coefficient denominators
     *   a_i = coeff_i * D   (now integers)
     *   g = gcd(|a_1|, ..., |a_k|)
     *   b_i = a_i / g        (primitive integer coefficients)
     *
     * Returns {poly, scale} where:
     *   - poly is an integer-coefficient PolyId in the given kernel
     *   - scale > 0 is a rational number
     *   - original_polynomial = scale * poly
     *
     * Because scale > 0, all relations (Eq, Neq, Lt, Leq, Gt, Geq)
     * are preserved without flipping.
     *
     * Returns nullopt-like result (poly == NullPoly) on construction failure.
     */
    struct NormalizedResult {
        PolyId poly = NullPoly;
        mpq_class scale = 1;  // positive
        bool ok() const { return poly != NullPoly; }
    };
    NormalizedResult toPrimitiveInteger(PolynomialKernel& kernel) const;

    /**
     * Reconstruct a RationalPolynomial from an existing integer-coefficient
     * PolyId.  Useful for rational substitution and other post-processing
     * that may introduce rational coefficients.
     */
    static std::optional<RationalPolynomial> fromPolyId(
        PolyId p, const PolynomialKernel& kernel);

private:
    FlatMonomialMap<mpq_class> terms_;

    static MonomialKey multiplyKeys(const MonomialKey& a, const MonomialKey& b);
    static MonomialKey powKey(const MonomialKey& a, uint32_t n);
};

} // namespace zolver
