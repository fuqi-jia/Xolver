#pragma once

#include "expr/ir.h"
#include <gmpxx.h>
#include <unordered_map>
#include <vector>

namespace xolver {

/**
 * ToRealLiteralFold (Capability 8b of the close-all-known-fails plan).
 *
 * Frontend, syntactic constant folding for the following patterns:
 *
 *   (to_real ConstInt k)             -> ConstReal (k)
 *   (to_real ConstReal r)            -> unchanged  (no-op; sometimes the
 *                                                   parser already gave us
 *                                                   a real literal)
 *   (/ ConstReal a ConstReal b)      -> ConstReal (a / b)    when b != 0
 *   (/ ConstReal a ConstReal 0)      -> unchanged  (SMT-LIB total-but-
 *                                                   underspecified; the
 *                                                   downstream
 *                                                   DivisionDefinitional-
 *                                                   Lowerer reports the
 *                                                   unsupported residual.)
 *
 * Pure constant folding; never adds assertions, never strengthens the
 * formula. Memoized walk; new ExprIds, never mutates.
 */
class ToRealLiteralFold {
public:
    explicit ToRealLiteralFold(CoreIr& ir);

    bool run();
    void commit();

private:
    ExprId foldRec(ExprId e);
    ExprId tryFoldToReal(ExprId node);
    ExprId tryFoldDivOfConsts(ExprId node);

    // Build a fresh ConstReal whose payload is value.get_str().
    ExprId mkConstReal(const mpq_class& value);

    CoreIr& ir_;
    SortId realSortId_;
    std::unordered_map<ExprId, ExprId> memo_;
    std::vector<std::pair<ScopeLevel, ExprId>> folded_;
};

} // namespace xolver
