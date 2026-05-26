#pragma once

#include <gmpxx.h>
#include <string>
#include <stdexcept>

namespace zolver {

/**
 * Safely construct mpq_class from a string, handling scientific notation
 * (e.g. "-3.5e-08", "1.23E+4") that GMP's mpq_set_str does not support.
 */
inline mpq_class mpqFromString(const std::string& str) {
    // Fast path: no scientific notation -> delegate to GMP directly
    if (str.find_first_of("eE") == std::string::npos) {
        return mpq_class(str);
    }

    // Parse mantissa and exponent
    size_t ePos = str.find_first_of("eE");
    std::string mantissa = str.substr(0, ePos);
    long long exp = std::stoll(str.substr(ePos + 1));

    // Split mantissa into integer and fractional parts
    size_t dotPos = mantissa.find('.');
    std::string intPart, fracPart;
    if (dotPos != std::string::npos) {
        intPart = mantissa.substr(0, dotPos);
        fracPart = mantissa.substr(dotPos + 1);
    } else {
        intPart = mantissa;
    }

    // Extract sign
    bool negative = false;
    if (!intPart.empty() && intPart[0] == '-') {
        negative = true;
        intPart = intPart.substr(1);
    } else if (!intPart.empty() && intPart[0] == '+') {
        intPart = intPart.substr(1);
    }

    // Strip leading zeros from integer part and trailing zeros from fractional part
    while (!intPart.empty() && intPart[0] == '0') intPart.erase(0, 1);
    while (!fracPart.empty() && fracPart.back() == '0') fracPart.pop_back();

    // Combine digits
    std::string digits = intPart + fracPart;
    if (digits.empty()) digits = "0";

    mpz_class num(digits);
    if (negative) num = -num;

    long long decimalPlaces = static_cast<long long>(fracPart.size());
    long long netExp = exp - decimalPlaces;

    if (netExp >= 0) {
        mpz_class pow10;
        mpz_ui_pow_ui(pow10.get_mpz_t(), 10, static_cast<unsigned long long>(netExp));
        return mpq_class(num * pow10, mpz_class(1));
    } else {
        mpz_class pow10;
        mpz_ui_pow_ui(pow10.get_mpz_t(), 10, static_cast<unsigned long long>(-netExp));
        return mpq_class(num, pow10);
    }
}

} // namespace zolver
