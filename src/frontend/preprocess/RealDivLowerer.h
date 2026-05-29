#pragma once

#include "expr/ir.h"
#include <vector>
#include <unordered_map>

namespace xolver {

/**
 * RealDivLowerer: purifies real division by a NON-constant denominator into a
 * fresh variable plus a guarded polynomial defining constraint, so the
 * nonlinear-real engine (CDCAC) can reason about it.
 *
 * Real `/` by a numeric constant is already handled by the PolynomialConverter
 * (poly * 1/c). Real `/` by a variable / compound term is NOT a polynomial, so
 * the atomizer rejects the enclosing atom and the solver returns `unknown`.
 *
 * Transformation — for `(/ a b)` with `b` not a numeric constant:
 *   replace term with fresh real `q`, and assert
 *       (=> (not (= b 0)) (= (* q b) a))
 *
 * Soundness (SMT-LIB real division is total, with `(/ a 0)` unconstrained):
 *   - b != 0: q*b = a pins q = a/b exactly.
 *   - b == 0: guard is false, q is free — matching the spec's underspecified
 *     div-by-zero. (The cross-term functional-consistency corner — distinct
 *     `(/ a 0)` and `(/ a' 0)` with a=a' allowed to differ here — is caught by
 *     the SAT model-validation floor over the original assertions.)
 * Every original model extends (set q = original value), so no false UNSAT;
 * the added constraint only tightens the b!=0 case to the unique correct value.
 *
 * Memoized by ExprId: syntactically identical division terms (hash-consed to
 * one ExprId) share ONE fresh q, preserving functional consistency.
 *
 * Only real-sorted Div is touched; integer div/mod is handled earlier by
 * IntDivModLowerer. Runs after UfInArithPurifier (denominators already clean
 * of UF applications) and before atomization.
 */
class RealDivLowerer {
public:
    explicit RealDivLowerer(CoreIr& ir);

    bool run();
    void commit();

    const std::vector<ExprId>& generatedAssertions() const { return generatedAssertions_; }

private:
    CoreIr& ir_;
    std::unordered_map<ExprId, ExprId> memo_;
    std::vector<ExprId> generatedAssertions_;
    bool changed_ = false;

    ExprId purifyRec(ExprId root);
    ExprId rebuildLike(ExprId original, const std::vector<ExprId>& newChildren);
    ExprId mkConstRealZero();
    ExprId mkEq(ExprId a, ExprId b);
    ExprId mkNot(ExprId a);
    ExprId mkImplies(ExprId a, ExprId b);
    ExprId mkMul(ExprId a, ExprId b);

    // True if `eid` is a nonzero-or-nonconstant denominator that the polynomial
    // converter cannot fold — i.e. anything NOT a ConstInt/ConstReal node.
    bool denomNeedsPurify(ExprId eid) const;
};

} // namespace xolver
