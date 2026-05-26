// LibpolyAlgebraic.cpp — implements the RealValue algebraic operations
// (declared in util/RealAlgebraicOps.h) by delegating to libpoly's
// algebraic-number module.  This is the only translation unit for RealValue
// arithmetic that pulls in <polyxx.h>.
//
// Strategy:
//   * Convert each RealValue operand to a poly::AlgebraicNumber.  Rationals use
//     lp_algebraic_number_construct_from_rational.  Algebraics are rebuilt by
//     RE-ISOLATING the real roots of the stored defining polynomial and
//     selecting the one inside the stored isolation interval — robust even when
//     the stored mpq interval is not dyadic (libpoly's intervals always are).
//   * Run the libpoly op, then COLLAPSE the result back to an exact Rational
//     RealValue when lp_algebraic_number_is_rational reports so (e.g. √2·√2→2);
//     otherwise extract the result's defining polynomial + dyadic interval.

#include "util/RealAlgebraicOps.h"

#include <stdexcept>

#ifdef ZOLVER_HAS_LIBPOLY

#include <polyxx.h>
#include <gmpxx.h>
#include <vector>

namespace zolver::realalg {

namespace {

// lp_rational_t / lp_integer_t are GMP __mpq_struct / __mpz_struct underneath,
// which is exactly why poly::detail::cast_to_gmp exists.  We bridge through the
// GMP element pointers.
static_assert(sizeof(lp_rational_t) == sizeof(__mpq_struct), "lp_rational_t must be GMP mpq");
static_assert(sizeof(lp_integer_t) == sizeof(__mpz_struct), "lp_integer_t must be GMP mpz");

const lp_rational_t* asLpRational(const mpq_class& q) {
    return reinterpret_cast<const lp_rational_t*>(q.get_mpq_t());
}

mpz_class dyadicToMpq_num(const poly::DyadicRational& dr) {
    poly::Integer n = poly::numerator(dr);
    return *poly::detail::cast_to_gmp(&n);
}
mpz_class dyadicToMpq_den(const poly::DyadicRational& dr) {
    poly::Integer d = poly::denominator(dr);
    return *poly::detail::cast_to_gmp(&d);
}
mpq_class dyadicToMpq(const poly::DyadicRational& dr) {
    mpq_class r(dyadicToMpq_num(dr), dyadicToMpq_den(dr));
    r.canonicalize();
    return r;
}

// Build a libpoly algebraic number from a RealValue.
poly::AlgebraicNumber toLp(const RealValue& v) {
    if (v.isRational()) {
        lp_algebraic_number_t tmp;
        lp_algebraic_number_construct_from_rational(&tmp, asLpRational(v.asRational()));
        poly::AlgebraicNumber result(&tmp);
        lp_algebraic_number_destruct(&tmp);
        return result;
    }
    const AlgebraicNumber& a = v.asAlgebraic();
    std::vector<poly::Integer> coeffs;          // low-to-high, same as our layout
    coeffs.reserve(a.coefficients.size());
    for (const auto& c : a.coefficients) coeffs.emplace_back(c);
    poly::UPolynomial up(coeffs);
    std::vector<poly::AlgebraicNumber> roots = poly::isolate_real_roots(up);
    poly::Rational lo(a.lower), hi(a.upper);
    for (auto& r : roots) {
        if (r >= lo && r <= hi) return std::move(r);
    }
    throw std::domain_error("RealValue: algebraic isolation interval contains no root of its defining polynomial");
}

// Convert a libpoly algebraic number back to a RealValue, collapsing to an
// exact Rational when libpoly reports it is rational.
RealValue fromLp(const poly::AlgebraicNumber& an) {
    if (poly::is_rational(an)) {
        mpq_t q;
        mpq_init(q);
        lp_algebraic_number_to_rational(an.get_internal(), reinterpret_cast<lp_rational_t*>(q));
        mpq_class result(q);
        result.canonicalize();
        mpq_clear(q);
        return RealValue::fromMpq(result);
    }
    // Defining polynomial coefficients (low-to-high).
    poly::UPolynomial def = poly::get_defining_polynomial(an);
    const lp_upolynomial_t* lpu = def.get_internal();
    size_t deg = lp_upolynomial_degree(lpu);
    std::vector<lp_integer_t> raw(deg + 1);
    for (auto& z : raw) mpz_init(reinterpret_cast<mpz_ptr>(&z));
    lp_upolynomial_unpack(lpu, raw.data());
    AlgebraicNumber out;
    out.coefficients.reserve(deg + 1);
    for (size_t i = 0; i <= deg; ++i) {
        out.coefficients.emplace_back(mpz_class(reinterpret_cast<mpz_srcptr>(&raw[i])));
        mpz_clear(reinterpret_cast<mpz_ptr>(&raw[i]));
    }
    const lp_algebraic_number_t* internal = an.get_internal();
    out.lower = dyadicToMpq(poly::get_lower_bound(an));
    out.upper = dyadicToMpq(poly::get_upper_bound(an));
    out.lowerOpen = internal->I.a_open != 0;
    out.upperOpen = internal->I.b_open != 0;
    return RealValue::fromAlgebraic(std::move(out));
}

enum class Bin { Add, Sub, Mul, Div };

RealValue binop(Bin op, const RealValue& a, const RealValue& b) {
    poly::AlgebraicNumber la = toLp(a);
    poly::AlgebraicNumber lb = toLp(b);
    // The libpoly op destructs its output before assigning, so it MUST be
    // pre-constructed.
    lp_algebraic_number_t res;
    lp_algebraic_number_construct_zero(&res);
    switch (op) {
        case Bin::Add: lp_algebraic_number_add(&res, la.get_internal(), lb.get_internal()); break;
        case Bin::Sub: lp_algebraic_number_sub(&res, la.get_internal(), lb.get_internal()); break;
        case Bin::Mul: lp_algebraic_number_mul(&res, la.get_internal(), lb.get_internal()); break;
        case Bin::Div: lp_algebraic_number_div(&res, la.get_internal(), lb.get_internal()); break;
    }
    poly::AlgebraicNumber wrapped(&res);
    lp_algebraic_number_destruct(&res);
    return fromLp(wrapped);
}

}  // namespace

RealValue add(const RealValue& a, const RealValue& b) { return binop(Bin::Add, a, b); }
RealValue sub(const RealValue& a, const RealValue& b) { return binop(Bin::Sub, a, b); }
RealValue mul(const RealValue& a, const RealValue& b) { return binop(Bin::Mul, a, b); }
RealValue div(const RealValue& a, const RealValue& b) {
    if (sign(b) == 0) throw std::domain_error("RealValue: division by zero");
    return binop(Bin::Div, a, b);
}
RealValue neg(const RealValue& a) {
    poly::AlgebraicNumber la = toLp(a);
    lp_algebraic_number_t res;
    lp_algebraic_number_construct_zero(&res);
    lp_algebraic_number_neg(&res, la.get_internal());
    poly::AlgebraicNumber wrapped(&res);
    lp_algebraic_number_destruct(&res);
    return fromLp(wrapped);
}

int compare(const RealValue& a, const RealValue& b) {
    poly::AlgebraicNumber la = toLp(a);
    poly::AlgebraicNumber lb = toLp(b);
    int c = lp_algebraic_number_cmp(la.get_internal(), lb.get_internal());
    return (c < 0) ? -1 : (c > 0) ? 1 : 0;
}

int sign(const RealValue& a) {
    if (a.isRational()) {
        const mpq_class& q = a.asRational();
        return (q > 0) ? 1 : (q < 0) ? -1 : 0;
    }
    poly::AlgebraicNumber la = toLp(a);
    int s = lp_algebraic_number_sgn(la.get_internal());
    return (s < 0) ? -1 : (s > 0) ? 1 : 0;
}

bool isExactInteger(const RealValue& a) {
    poly::AlgebraicNumber la = toLp(a);
    mpz_t fl, cl;
    mpz_init(fl);
    mpz_init(cl);
    lp_algebraic_number_floor(la.get_internal(), reinterpret_cast<lp_integer_t*>(fl));
    lp_algebraic_number_ceiling(la.get_internal(), reinterpret_cast<lp_integer_t*>(cl));
    bool eq = (mpz_cmp(fl, cl) == 0);
    mpz_clear(fl);
    mpz_clear(cl);
    return eq;
}

mpz_class floorOf(const RealValue& a) {
    poly::AlgebraicNumber la = toLp(a);
    mpz_t r;
    mpz_init(r);
    lp_algebraic_number_floor(la.get_internal(), reinterpret_cast<lp_integer_t*>(r));
    mpz_class result(r);
    mpz_clear(r);
    return result;
}

mpz_class ceilOf(const RealValue& a) {
    poly::AlgebraicNumber la = toLp(a);
    mpz_t r;
    mpz_init(r);
    lp_algebraic_number_ceiling(la.get_internal(), reinterpret_cast<lp_integer_t*>(r));
    mpz_class result(r);
    mpz_clear(r);
    return result;
}

} // namespace zolver::realalg

#else  // !ZOLVER_HAS_LIBPOLY — stub fallback (algebraic unsupported)

namespace zolver::realalg {
namespace {
[[noreturn]] void unsupported() {
    throw std::logic_error("RealValue: algebraic arithmetic requires libpoly (ZOLVER_HAS_LIBPOLY)");
}
}
RealValue add(const RealValue&, const RealValue&) { unsupported(); }
RealValue sub(const RealValue&, const RealValue&) { unsupported(); }
RealValue mul(const RealValue&, const RealValue&) { unsupported(); }
RealValue div(const RealValue&, const RealValue&) { unsupported(); }
RealValue neg(const RealValue&)                   { unsupported(); }
int compare(const RealValue&, const RealValue&)   { unsupported(); }
int sign(const RealValue&)                        { unsupported(); }
bool isExactInteger(const RealValue&)             { unsupported(); }
mpz_class floorOf(const RealValue&)               { unsupported(); }
mpz_class ceilOf(const RealValue&)                { unsupported(); }
} // namespace zolver::realalg

#endif
