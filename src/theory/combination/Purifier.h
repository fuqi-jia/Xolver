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

    // (#77) Bridge COMPOUND arith UF arguments into fresh shared leaves so the
    // model-based arrangement can fire UF congruence over arith-equal args
    // (closes the QF_UFLIA/UFLRA false-sat class). Enabled ONLY by the pure
    // UF-arith builders — NOT datatype/array, where it perturbs the DtReasoner /
    // array axioms. Legacy XOLVER_COMB_SAT_FLOOR/UFARG_ARRANGE still force it on.
    void setUfArgBridge(bool v) { ufArgBridge_ = v; }

    void run();

    const std::vector<ExprId>& bridgeAssertions() const { return bridgeAssertions_; }

private:
    CoreIr& ir_;
    SharedTermRegistry& registry_;
    SortId boolSortId_;
    TheoryId arithTheory_ = TheoryId::LRA;
    bool ufArgBridge_ = false;   // (#77) set by pure UF-arith builders only

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
    ExprId makeNot(ExprId child);
    ExprId makeOr(ExprId a, ExprId b);

    // (#69) store-vs-base extensionality, gated default-OFF
    // (XOLVER_AX_STORE_VS_BASE). For each ASSERTED equality atom `(= s c)` where
    // `s = store(c, j, v)` is a store directly over the other side `c`, add the
    // sound biconditional axiom  (s = c) ⟺ (select(c, j) = v)  as two boolean
    // clauses. This is a VALID array-theory lemma (read-over-write + store-is-
    // identity-when-value-already-present), so it never removes or adds models;
    // it only lets the Boolean layer unit-propagate the *disequality* direction
    // `select(c, j) ≠ v` into arith via the normal interface-disequality path.
    // Closes the compound-value store-vs-base completeness floor that otherwise
    // leaves the validator at `unknown`. The `(= s c)` atom is REUSED (exact
    // ExprId) so the axiom binds the very atom the assertion pins; `select(c, j)`
    // is bridged into a fresh shared leaf so the equality routes to Combination.
    void addStoreVsBaseAxioms();

    TheoryId theoryOf(ExprId eid) const;

    ExprId purifyRec(ExprId eid);
    void purifyAssertion(ExprId eid);
    void registerEufVars(ExprId eid);
};

} // namespace xolver
