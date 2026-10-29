#include "applications/satisfiability/smt/qffp/Arithmetic.h"
#include <algorithm>
#include <climits>
namespace xolver::applications::satisfiability::smt::fp {
namespace {
struct Value {
    bool sign = false, infinite = false, nan = false;
    mpq_class number = 0;
};
class Binary {
    std::size_t e, s;
    WorkBudget &budget;
    mpz_class exponentMask, hidden, signMask;
    long bias;
    mpq_class power(long exponent) {
        const unsigned long magnitude =
            exponent < 0 ? static_cast<unsigned long>(-(exponent + 1)) + 1 : exponent;
        budget.tick(magnitude);
        mpz_class n = mpz_class(1) << magnitude;
        return exponent < 0 ? mpq_class(1, n) : mpq_class(n);
    }
    mpz_class sign(const mpz_class &bits, bool negative) const {
        return negative ? bits + signMask : bits;
    }
    mpz_class overflow(bool negative, Rounding rounding) const {
        const bool infinity = rounding == Rounding::NearestEven ||
                              rounding == Rounding::NearestAway ||
                              (rounding == Rounding::Positive && !negative) ||
                              (rounding == Rounding::Negative && negative);
        return infinity ? inf(negative)
                        : sign(((exponentMask - 1) << (s - 1)) + hidden - 1, negative);
    }

  public:
    Binary(std::size_t eb, std::size_t sb, WorkBudget &work) : e(eb), s(sb), budget(work) {
        if (e < 2 || s < 2)
            throw std::invalid_argument("invalid binary floating-point format");
        if (e >= sizeof(long) * CHAR_BIT || s > static_cast<std::size_t>(LONG_MAX / 4))
            throw ResourceExhausted("floating-point exponent representation exhausted");
        budget.tick(e);
        budget.tick(s);
        exponentMask = (mpz_class(1) << e) - 1;
        hidden = mpz_class(1) << (s - 1);
        signMask = mpz_class(1) << (e + s - 1);
        bias = static_cast<long>((1UL << (e - 1)) - 1);
    }
    mpz_class inf(bool negative) const { return sign(exponentMask << (s - 1), negative); }
    mpz_class nan() const { return (exponentMask << (s - 1)) + 1; }
    mpz_class zero(bool negative) const { return negative ? signMask : mpz_class(0); }
    Value decode(const mpz_class &bits) {
        Value v;
        v.sign = mpz_tstbit(bits.get_mpz_t(), e + s - 1);
        const mpz_class exponent = (bits >> (s - 1)) & exponentMask;
        const mpz_class fraction = bits & (hidden - 1);
        if (exponent == exponentMask) {
            v.infinite = fraction == 0;
            v.nan = fraction != 0;
            return v;
        }
        mpz_class mantissa = fraction + (exponent == 0 ? mpz_class(0) : hidden);
        if (mantissa == 0)
            return v;
        long shift = (exponent == 0 ? 1 : exponent.get_si()) - bias - static_cast<long>(s - 1);
        v.number = mpq_class(mantissa) * power(shift);
        if (v.sign)
            v.number = -v.number;
        return v;
    }
    mpz_class rounded(mpq_class number, bool zeroSign, Rounding rounding) {
        if (number == 0)
            return zero(zeroSign);
        const bool negative = number < 0;
        if (negative)
            number = -number;
        const auto nb = mpz_sizeinbase(number.get_num_mpz_t(), 2),
                   db = mpz_sizeinbase(number.get_den_mpz_t(), 2);
        if (nb > LONG_MAX / 4 || db > LONG_MAX / 4)
            throw ResourceExhausted("floating-point magnitude exhausted");
        long exponent = static_cast<long>(nb) - static_cast<long>(db);
        if (number < power(exponent))
            --exponent;
        const long minimum = 1 - bias, maximum = bias;
        if (exponent > maximum)
            return overflow(negative, rounding);
        const long effective = std::max(exponent, minimum);
        const mpq_class scaled = number / power(effective - static_cast<long>(s - 1));
        mpz_class integral, remainder;
        mpz_fdiv_qr(integral.get_mpz_t(), remainder.get_mpz_t(), scaled.get_num_mpz_t(),
                    scaled.get_den_mpz_t());
        const mpz_class twice = 2 * remainder;
        const bool increment =
            remainder != 0 && (rounding == Rounding::NearestEven
                                   ? twice > scaled.get_den() || (twice == scaled.get_den() &&
                                                                  mpz_odd_p(integral.get_mpz_t()))
                               : rounding == Rounding::NearestAway ? twice >= scaled.get_den()
                               : rounding == Rounding::Positive    ? !negative
                               : rounding == Rounding::Negative    ? negative
                                                                   : false);
        if (increment)
            ++integral;
        if (integral == 0)
            return zero(negative);
        if (integral < hidden)
            return sign(integral, negative);
        exponent = effective;
        if (integral >= 2 * hidden) {
            integral >>= 1;
            ++exponent;
        }
        if (exponent > maximum)
            return overflow(negative, rounding);
        return sign((mpz_class(exponent + bias) << (s - 1)) + integral - hidden, negative);
    }
};
} // namespace
mpz_class evaluate(Arithmetic operation, Rounding rounding, std::size_t e, std::size_t s,
                   const mpz_class &left, const mpz_class &right, WorkBudget &budget) {
    Binary b(e, s, budget);
    auto x = b.decode(left), y = b.decode(right);
    if (x.nan || y.nan)
        return b.nan();
    if (operation == Arithmetic::Subtract) {
        y.sign = !y.sign;
        y.number = -y.number;
        operation = Arithmetic::Add;
    }
    if (operation == Arithmetic::Add) {
        if (x.infinite || y.infinite) {
            if (x.infinite && y.infinite && x.sign != y.sign)
                return b.nan();
            return b.inf(x.infinite ? x.sign : y.sign);
        }
        const bool negativeZero = x.number == 0 && y.number == 0 && x.sign == y.sign
                                      ? x.sign
                                      : rounding == Rounding::Negative;
        return b.rounded(x.number + y.number, negativeZero, rounding);
    }
    const bool negative = x.sign != y.sign;
    if (operation == Arithmetic::Multiply) {
        if ((x.infinite && y.number == 0 && !y.infinite) ||
            (y.infinite && x.number == 0 && !x.infinite))
            return b.nan();
        if (x.infinite || y.infinite)
            return b.inf(negative);
        return b.rounded(x.number * y.number, negative, rounding);
    }
    if (operation != Arithmetic::Divide)
        throw std::invalid_argument("unknown FP arithmetic operation");
    if ((x.infinite && y.infinite) ||
        (!x.infinite && !y.infinite && x.number == 0 && y.number == 0))
        return b.nan();
    if (x.infinite)
        return b.inf(negative);
    if (y.infinite)
        return b.zero(negative);
    if (y.number == 0)
        return b.inf(negative);
    return b.rounded(x.number / y.number, negative, rounding);
}
} // namespace xolver::applications::satisfiability::smt::fp
