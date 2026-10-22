#pragma once
#include <gmpxx.h>
#include <string>

namespace xolver {
// Decimal integer field syntax shared by SL construction and evidence replay.
inline bool integerLiteral(const std::string& text, mpz_class& value) {
    if (text.empty()) return false;
    const std::size_t first = text[0] == '-' ? 1 : 0;
    if (first == text.size()) return false;
    for (std::size_t i = first; i < text.size(); ++i)
        if (text[i] < '0' || text[i] > '9') return false;
    return value.set_str(text, 10) == 0;
}
} // namespace xolver
