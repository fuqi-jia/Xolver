#pragma once

#include "expr/types.h"
#include "expr/ir.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include <unordered_map>

namespace nlcolver {

/**
 * Convert NLColver CoreIr arithmetic expressions into PolyId polynomials
 * via a PolynomialKernel.
 *
 * Handles:
 *   ConstInt, ConstReal  → mkConst
 *   Variable             → mkVar
 *   Add, Sub, Neg, Mul   → add, sub, neg, mul
 *   Pow                  → pow
 *
 * Non-arithmetic nodes (And, Or, etc.) are rejected and return NullPoly.
 */
class PolynomialConverter {
public:
    explicit PolynomialConverter(PolynomialKernel& kernel)
        : kernel_(kernel) {}

    PolyId convert(ExprId eid, const CoreIr& ir);

private:
    PolynomialKernel& kernel_;
    std::unordered_map<ExprId, PolyId> memo_;

    PolyId convertRec(ExprId eid, const CoreIr& ir);
};

} // namespace nlcolver
