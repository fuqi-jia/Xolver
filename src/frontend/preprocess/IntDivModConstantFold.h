#pragma once

#include "expr/ir.h"
#include <unordered_map>
#include <vector>

namespace nlcolver {

/**
 * IntDivModConstantFold (Capability 8e' of the close-all-known-fails plan).
 *
 * Constant-folding pass for integer div/mod under SMT-LIB integer-division
 * semantics. Runs BEFORE IntDivModLowerer (Cap 8e) so that constant-divisor /
 * constant-dividend cases are reduced to literal `ConstInt`s without
 * introducing fresh quotient/remainder variables.
 *
 * Rewrites (only when both operands are constant integers with `b != 0`):
 *
 *   (div a b)  -->  ConstInt (a div_T b)
 *   (mod a b)  -->  ConstInt (a mod_T b)
 *
 * where `q = div_T(a, b)` and `r = mod_T(a, b)` are the SMT-LIB integer
 * quotient/remainder satisfying `a = b*q + r` with `0 <= r < |b|`.
 *
 * Cases with non-constant operand or `b = 0` are left untouched and are
 * picked up by Cap 8e (IntDivModLowerer) which introduces the standard
 * fresh-variable definitional axioms.
 *
 * Pure constant folding; never adds assertions, never strengthens the
 * formula. Memoized walk; new ExprIds, never mutates.
 */
class IntDivModConstantFold {
public:
    explicit IntDivModConstantFold(CoreIr& ir);

    bool run();
    void commit();

    bool didFold() const { return didFold_; }

private:
    ExprId foldRec(ExprId e);
    ExprId tryFoldDivMod(ExprId node);

    ExprId mkConstInt(int64_t v);

    CoreIr& ir_;
    SortId intSortId_;
    std::unordered_map<ExprId, ExprId> memo_;
    std::vector<std::pair<ScopeLevel, ExprId>> folded_;
    bool didFold_ = false;
};

} // namespace nlcolver
