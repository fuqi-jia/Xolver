#pragma once

#include "expr/ir.h"
#include <unordered_map>
#include <vector>

namespace xolver {

/**
 * BoolSubtermPurifier: eliminates boolean composite expressions from
 * non-boolean-atomic positions (e.g. UFApply arguments, equality arguments).
 *
 * Example:
 *   (Q (not a))  →  (Q b)  with  b = (not a)
 *
 * Invariant:
 *   - Pure IR-to-IR, no SAT/theory interaction.
 *   - Generated assertions are added at scope 0 (global).
 */
class BoolSubtermPurifier {
public:
    explicit BoolSubtermPurifier(CoreIr& ir);

    // Run purification. Returns true if any change happened.
    bool run();

    // Commit generated equivalence constraints to CoreIr.
    void commit();

private:
    ExprId purifyRec(ExprId root, bool inArgPosition);
    bool isBoolComposite(ExprId e) const;

    // Rebuild node with new children
    ExprId rebuildLike(ExprId original, const std::vector<ExprId>& newChildren);

    // IR builders
    ExprId mkEq(ExprId a, ExprId b);
    ExprId mkAnd(ExprId a, ExprId b);
    ExprId mkOr(ExprId a, ExprId b);
    ExprId mkImplies(ExprId a, ExprId b);
    ExprId mkNot(ExprId a);
    ExprId mkDistinct(ExprId a, ExprId b);

    CoreIr& ir_;
    SortId boolSortId_;
    std::unordered_map<ExprId, ExprId> memo_;
    std::vector<ExprId> generatedAssertions_;
    bool changed_ = false;
};

} // namespace xolver
