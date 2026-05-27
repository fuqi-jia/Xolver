#pragma once

#include "expr/types.h"
#include "expr/ir.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include "theory/arith/poly/RationalPolynomial.h"
#include <gmpxx.h>
#include <optional>
#include <unordered_map>

namespace zolver {

enum class PolyConstraintStatus {
    Constraint,            // normal polynomial constraint
    Tautology,             // always true (e.g. 0 <= 0)
    Conflict,              // always false (e.g. 0 < 0)
    UnsupportedNonPolynomial, // expression is not a polynomial
    Failure                // construction failure
};

/**
 * Convert Zolver CoreIr arithmetic expressions into PolyId polynomials
 * via a PolynomialKernel.
 *
 * Design: two-phase conversion.
 *   Phase 1: collect a RationalPolynomial from the expression tree.
 *   Phase 2: normalize to a primitive integer-coefficient polynomial.
 *
 * This guarantees that all PolyIds returned are integer-coefficient,
 * satisfying the LibPolyKernel invariant, while fully supporting
 * rational coefficients in the input.
 *
 * Handles: ConstInt, ConstReal, Variable, Add, Sub, Neg, Mul, Pow,
 *          Div by numeric constant.
 * Non-polynomial nodes (e.g. division by variable, negative exponent)
 * return UnsupportedNonPolynomial.
 */
class PolynomialConverter {
public:
    explicit PolynomialConverter(PolynomialKernel& kernel)
        : kernel_(kernel) {}

    /** Convert a single expression. Returns {poly, scale} where
     *  original_expr = scale * poly, scale > 0.
     *  Returns !ok() for unsupported non-polynomial expressions.
     */
    struct ConvertedExpr {
        PolyId poly = NullPoly;
        mpq_class scale = 1;  // positive
        bool ok() const { return poly != NullPoly; }
    };
    ConvertedExpr convert(ExprId eid, const CoreIr& ir);

    /** Convert a constraint lhs rel rhs.
     *  Returns the integer polynomial (lhs - rhs) with status, or failure.
     */
    struct ConvertedConstraint {
        PolyConstraintStatus status = PolyConstraintStatus::Failure;
        PolyId diff = NullPoly;  // integer poly representing (lhs - rhs)
        bool isConstraint() const { return status == PolyConstraintStatus::Constraint; }
    };
    ConvertedConstraint convertConstraint(ExprId lhs, ExprId rhs,
                                          Relation rel, const CoreIr& ir);

private:
    PolynomialKernel& kernel_;
    std::unordered_map<ExprId, std::optional<RationalPolynomial>> memo_;

    std::optional<RationalPolynomial> collectRec(ExprId eid, const CoreIr& ir);
    // Iterative bottom-up pre-pass that memoizes nested arith subterms so
    // collectRec never recurses deeply (deep-term stack-overflow guard).
    void preCollectIterative(ExprId root, const CoreIr& ir);
};

} // namespace zolver
