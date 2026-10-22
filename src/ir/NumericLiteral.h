#pragma once
#include "ir/NativeTerms.h"
#include <gmpxx.h>
#include <optional>

namespace xolver {
// The single decoder for numeric IR payloads. A malformed payload, including
// a fractional Int, is not a numeric constant. No GMP zero-denominator trap.
std::optional<mpq_class> numericLiteral(const TermExpr&);
std::optional<mpq_class> numericLiteral(const NativeTerms&, ExprId);
} // namespace xolver
