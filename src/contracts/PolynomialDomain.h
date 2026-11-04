#pragma once

#include "ir/types.h"
#include <span>

namespace xolver {

// Domain facts supplied by the typed problem, never by a candidate model.
// Unlisted variables remain real unless the whole context is integral.
struct PolynomialDomain {
    bool allInteger = false;
    std::span<const VarId> integerVariables{};
};

} // namespace xolver
