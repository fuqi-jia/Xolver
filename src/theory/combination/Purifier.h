#pragma once
#include "expr/ir.h"
#include "theory/combination/SharedTermRegistry.h"
#include <vector>
#include <string>
#include <unordered_set>

namespace xolver {

/**
 * Purifier for Nelson-Oppen theory combination.
 *
 * Decomposes mixed assertions into:
 *   - Pure theory atoms (one owner each)
 *   - Bridge definitions: fresh_var = alien_subterm
 *   - Shared equality atoms between shared constants
 *
 * Runs BEFORE atomization. Operates directly on CoreIr.
 */
class Purifier {
public:
    Purifier(CoreIr& ir, SharedTermRegistry& registry, SortId boolSort);

    void setArithTheory(TheoryId theory) { arithTheory_ = theory; }

    void run();

    const std::vector<ExprId>& bridgeAssertions() const { return bridgeAssertions_; }

private:
    CoreIr& ir_;
    SharedTermRegistry& registry_;
    SortId boolSortId_;
    TheoryId arithTheory_ = TheoryId::LRA;

    std::vector<ExprId> bridgeAssertions_;
    uint32_t freshCounter_ = 0;
    std::unordered_map<ExprId, ExprId> cache_;
    // Phase 1: compound UF-argument -> its bridge variable, so identical compound
    // args (hash-consed to the same ExprId) reuse ONE shared leaf. Without this,
    // f(t)=f(t) becomes f(b0)=f(b1) with distinct bridge vars that merely coincide
    // -> a spurious congruence obligation (over-floor of a trivially-sat formula).
    std::unordered_map<ExprId, ExprId> ufArgBridgeCache_;

    bool containsUfApply(ExprId eid) const;
    bool containsArithmetic(ExprId eid) const;

    // True if `eid` is an array operator (select/store/const-array).
    static bool isArrayOp(const CoreExpr& e);
    // True if `eid` is a compound arithmetic term (Add/Sub/Mul/...) — i.e. NOT
    // a bare variable or numeric constant. Such terms in array index/element
    // positions must be replaced by a fresh shared bridge variable so EUF and
    // the arith theory agree on the same shared leaf.
    bool isCompoundArith(ExprId eid) const;

    ExprId makeFreshVar(SortId sort);
    ExprId makeEq(ExprId lhs, ExprId rhs);

    TheoryId theoryOf(ExprId eid) const;

    ExprId purifyRec(ExprId eid);
    void purifyAssertion(ExprId eid);
    void registerEufVars(ExprId eid);
};

} // namespace xolver
