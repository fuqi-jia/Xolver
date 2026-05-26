#pragma once

#include "expr/ir.h"
#include <unordered_map>
#include <vector>

namespace zolver {

struct CastNormalizeResult {
    std::vector<std::pair<ScopeLevel, ExprId>> assertions;
};

/**
 * ArithCastNormalizer: pure IR-to-IR pass that folds constant casts.
 *
 *   to_real(ConstInt)   -> ConstReal
 *   to_int(ConstReal)   -> ConstInt  (if result fits in int64_t)
 *   to_int(to_real(x))  -> x  (when x is Int-sorted)
 *
 * Does NOT eliminate non-constant to_int / to_real.
 * Those are handled by ToIntDefinitionalLowerer.
 */
class ArithCastNormalizer {
public:
    explicit ArithCastNormalizer(CoreIr& ir) : ir_(ir) {}
    CastNormalizeResult run();

private:
    CoreIr& ir_;
    std::unordered_map<ExprId, ExprId> memo_;
    ExprId rewriteRec(ExprId e);
};

} // namespace zolver
