#pragma once

#include <gmpxx.h>
#include <limits>
#include <stdexcept>
#include <string>

namespace xolver {
namespace rational_detail {
inline bool signedDigits(const std::string& text) {
    size_t i = !text.empty() && (text[0] == '-' || text[0] == '+') ? 1 : 0;
    if (i == text.size()) return false;
    for (; i < text.size(); ++i) if (text[i] < '0' || text[i] > '9') return false;
    return true;
}
inline mpz_class integer(const std::string& text) {
    if (!signedDigits(text)) throw std::invalid_argument("invalid integer literal");
    return mpz_class(text[0] == '+' ? text.substr(1) : text, 10);
}
}

// Exact canonical rational, decimal or scientific literal. Never pass a zero
// denominator into GMP canonicalization, which would raise SIGFPE rather than
// a C++ exception. Decimal parsing does not round through floating point.
inline mpq_class mpqFromString(const std::string& text) {
    if (text.empty()) throw std::invalid_argument("empty numeric literal");
    auto slash = text.find('/');
    if (slash != std::string::npos) {
        mpz_class numerator = rational_detail::integer(text.substr(0, slash));
        mpz_class denominator = rational_detail::integer(text.substr(slash + 1));
        if (denominator == 0) throw std::invalid_argument("zero rational denominator");
        mpq_class value(numerator, denominator);
        value.canonicalize();
        return value;
    }
    auto ePos = text.find_first_of("eE");
    long long exponent = 0;
    if (ePos != std::string::npos) {
        std::string expText = text.substr(ePos + 1);
        if (!rational_detail::signedDigits(expText))
            throw std::invalid_argument("invalid decimal exponent");
        exponent = std::stoll(expText);
    }
    std::string mantissa = text.substr(0, ePos);
    const bool negative = !mantissa.empty() && mantissa[0] == '-';
    size_t pos = !mantissa.empty() && (mantissa[0] == '-' || mantissa[0] == '+') ? 1 : 0;
    std::string digits;
    size_t decimalPlaces = 0;
    bool dot = false;
    for (; pos < mantissa.size(); ++pos) {
        char c = mantissa[pos];
        if (c == '.' && !dot) { dot = true; continue; }
        if (c < '0' || c > '9') throw std::invalid_argument("invalid numeric literal");
        digits += c;
        if (dot) ++decimalPlaces;
    }
    if (digits.empty()) throw std::invalid_argument("numeric literal has no digits");
    mpz_class numerator(digits, 10);
    if (numerator == 0) return mpq_class(0);
    if (negative) numerator = -numerator;
    if (decimalPlaces > static_cast<size_t>(std::numeric_limits<long long>::max()) ||
        exponent < std::numeric_limits<long long>::min() + static_cast<long long>(decimalPlaces))
        throw std::out_of_range("decimal exponent overflow");
    long long scale = exponent - static_cast<long long>(decimalPlaces);
    // Avoid negating LLONG_MIN when calculating the power's magnitude.
    unsigned long long magnitude = scale < 0
        ? static_cast<unsigned long long>(-(scale + 1)) + 1
        : static_cast<unsigned long long>(scale);
    if (magnitude > std::numeric_limits<unsigned long>::max())
        throw std::out_of_range("decimal exponent exceeds GMP exponent range");
    mpz_class power;
    mpz_ui_pow_ui(power.get_mpz_t(), 10, static_cast<unsigned long>(magnitude));
    mpq_class value = scale >= 0 ? mpq_class(numerator * power) : mpq_class(numerator, power);
    value.canonicalize();
    return value;
}

} // namespace xolver
