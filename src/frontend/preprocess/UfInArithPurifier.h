#pragma once

#include "expr/ir.h"
#include <vector>
#include <unordered_map>

namespace nlcolver {

/**
 * UfInArithPurifier: bridges uninterpreted-function applications that appear
 * inside arithmetic expressions into fresh variables.
 *
 * Example:
 *   (= (+ (* x x) (* (f x) (f x))) 1)
 * becomes:
 *   (= (+ (* x x) (* b0 b0)) 1)
 *   (= b0 (f x))
 *
 * This allows arithmetic solvers (LRA, LIA, NRA, NIA) to treat UF applications
 * as opaque variables while EUF still manages the function-symbol semantics.
 */
class UfInArithPurifier {
public:
    explicit UfInArithPurifier(CoreIr& ir);

    bool run();
    void commit();

private:
    CoreIr& ir_;
    std::unordered_map<ExprId, ExprId> memo_;
    std::vector<ExprId> generatedAssertions_;
    bool changed_ = false;

    ExprId purifyRec(ExprId e, bool inArithContext);
    ExprId rebuildLike(ExprId original, const std::vector<ExprId>& newChildren);
    ExprId mkEq(ExprId a, ExprId b);

    static bool isArithKind(Kind k);
};

} // namespace nlcolver
