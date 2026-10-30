#pragma once

#include "ir/types.h"
#include "ir/NativeTerms.h"
#include "algebra/poly/PolynomialKernel.h"
#include "algebra/poly/RationalPolynomial.h"
#include <gmpxx.h>
#include <optional>
#include <chrono>
#include <unordered_map>

namespace xolver {

class WorkBudget;

enum class PolyConstraintStatus {
    Constraint,            // normal polynomial constraint
    Tautology,             // always true (e.g. 0 <= 0)
    Conflict,              // always false (e.g. 0 < 0)
    UnsupportedNonPolynomial, // expression is not a polynomial
    Failure                // construction failure
};

/**
 * Convert Xolver NativeTerms arithmetic expressions into PolyId polynomials
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
    explicit PolynomialConverter(PolynomialKernel& kernel, WorkBudget* budget = nullptr,
        std::chrono::steady_clock::time_point deadline = std::chrono::steady_clock::time_point::max())
        : kernel_(kernel), budget_(budget), deadline_(deadline) {}

    /** Convert a single expression. Returns {poly, scale} where
     *  original_expr = scale * poly, scale > 0.
     *  Returns !ok() for unsupported non-polynomial expressions.
     */
    struct ConvertedExpr {
        PolyId poly = NullPoly;
        mpq_class scale = 1;  // positive
        bool ok() const { return poly != NullPoly; }
    };
    ConvertedExpr convert(ExprId eid, const NativeTerms& ir);

    /** Convert a constraint lhs rel rhs.
     *  Returns the integer polynomial (lhs - rhs) with status, or failure.
     */
    struct ConvertedConstraint {
        PolyConstraintStatus status = PolyConstraintStatus::Failure;
        PolyId diff = NullPoly;  // integer poly representing (lhs - rhs)
        bool isConstraint() const { return status == PolyConstraintStatus::Constraint; }
    };
    ConvertedConstraint convertConstraint(ExprId lhs, ExprId rhs,
                                          Relation rel, const NativeTerms& ir);

private:
    PolynomialKernel& kernel_;
    WorkBudget* budget_;
    std::chrono::steady_clock::time_point deadline_;
    std::unordered_map<ExprId, std::optional<RationalPolynomial>> memo_;

    void charge(size_t amount = 1);
    void chargeProduct(const RationalPolynomial&, const RationalPolynomial&);
    RationalPolynomial power(RationalPolynomial, uint32_t);

    std::optional<RationalPolynomial> collectRec(ExprId eid, const NativeTerms& ir);
    // Iterative bottom-up pre-pass that memoizes nested arith subterms so
    // collectRec never recurses deeply (deep-term stack-overflow guard).
    void preCollectIterative(ExprId root, const NativeTerms& ir);
};

} // namespace xolver
