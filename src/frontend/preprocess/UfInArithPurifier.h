#pragma once

#include "ir/NativeTerms.h"
#include <vector>
#include <unordered_map>

namespace xolver {

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
    explicit UfInArithPurifier(NativeTerms& ir);

    bool run();
    void commit();

private:
    NativeTerms& ir_;
    std::unordered_map<uint64_t, ExprId> memo_;
    std::vector<ExprId> generatedAssertions_;
    bool changed_ = false;

    ExprId purifyRec(ExprId e, bool inArithContext);
    ExprId rebuildLike(ExprId original, const std::vector<ExprId>& newChildren);
    ExprId mkEq(ExprId a, ExprId b);

    static bool isArithKind(Kind k);
    bool isArithPosition(const TermExpr& node, size_t child) const;
    static uint64_t memoKey(ExprId id, bool arithmetic) {
        return (uint64_t{id} << 1) | uint64_t{arithmetic};
    }
};

} // namespace xolver
