#include "frontend/preprocess/ZoharBwiAxiomEmitter.h"

#include <string>
#include <unordered_set>
#include <vector>

namespace xolver {

ZoharBwiAxiomEmitter::ZoharBwiAxiomEmitter(CoreIr& ir, SortId boolSortId)
    : ir_(ir), boolSortId_(boolSortId), intSortId_(ir.intSortId()) {}

bool ZoharBwiAxiomEmitter::isUfApplyNamed(const CoreExpr& node,
                                          std::string_view name) {
    if (node.kind != Kind::UFApply) return false;
    auto* s = std::get_if<std::string>(&node.payload.value);
    return s && std::string_view(*s) == name;
}

ExprId ZoharBwiAxiomEmitter::mkConstInt(int64_t v) {
    CoreExpr e;
    e.kind = Kind::ConstInt;
    e.sort = intSortId_;
    e.payload = Payload(v);
    return ir_.add(std::move(e));
}

ExprId ZoharBwiAxiomEmitter::mkGeq(ExprId a, ExprId b) {
    CoreExpr e;
    e.kind = Kind::Geq;
    e.sort = boolSortId_;
    e.children.push_back(a);
    e.children.push_back(b);
    return ir_.add(std::move(e));
}

ExprId ZoharBwiAxiomEmitter::mkEq(ExprId a, ExprId b) {
    CoreExpr e;
    e.kind = Kind::Eq;
    e.sort = boolSortId_;
    e.children.push_back(a);
    e.children.push_back(b);
    return ir_.add(std::move(e));
}

ExprId ZoharBwiAxiomEmitter::mkImplies(ExprId a, ExprId b) {
    CoreExpr e;
    e.kind = Kind::Implies;
    e.sort = boolSortId_;
    e.children.push_back(a);
    e.children.push_back(b);
    return ir_.add(std::move(e));
}

ExprId ZoharBwiAxiomEmitter::mkPow2(ExprId arg, SortId intSort) {
    CoreExpr e;
    e.kind = Kind::UFApply;
    e.sort = intSort;
    e.payload = Payload(std::string("pow2"));
    e.children.push_back(arg);
    return ir_.add(std::move(e));
}

void ZoharBwiAxiomEmitter::visit(ExprId root,
                                 std::unordered_set<ExprId>& visited,
                                 std::unordered_set<ExprId>& pow2Terms) const {
    std::vector<ExprId> stack{root};
    while (!stack.empty()) {
        ExprId id = stack.back();
        stack.pop_back();
        if (!visited.insert(id).second) continue;
        const CoreExpr& node = ir_.get(id);

        if (isUfApplyNamed(node, "pow2")) {
            // pow2 must be (Int) -> Int with exactly one argument; the Zohar
            // header is `(declare-fun pow2 (Int) Int)`. Skip otherwise — a
            // different `pow2` (with different arity) is not the encoding we
            // know how to axiomatize.
            if (node.children.size() == 1) pow2Terms.insert(id);
        }
        for (ExprId c : node.children) stack.push_back(c);
    }
}

void ZoharBwiAxiomEmitter::collectPow2Terms(
        std::unordered_set<ExprId>& out) const {
    std::unordered_set<ExprId> visited;
    for (ExprId a : ir_.assertions()) visit(a, visited, out);
}

bool ZoharBwiAxiomEmitter::run() {
    detected_ = false;
    axiomCount_ = 0;

    std::unordered_set<ExprId> pow2Terms;
    collectPow2Terms(pow2Terms);
    if (pow2Terms.empty()) return false;
    detected_ = true;

    // Sort term ids for deterministic axiom ordering (helps test stability +
    // makes downstream stages see a consistent assertion order across runs).
    std::vector<ExprId> sorted(pow2Terms.begin(), pow2Terms.end());
    std::sort(sorted.begin(), sorted.end());

    SortId intSort = ir_.intSortId();
    ExprId zero = mkConstInt(0);
    ExprId one  = mkConstInt(1);

    // Ground: (= (pow2 0) 1). Emitted exactly once, regardless of whether
    // (pow2 0) syntactically appears — it always evaluates to 1 under the
    // standard semantics and pins pow2 at its base case for any later
    // recursive axiom (Phase 2).
    ExprId pow2OfZero = mkPow2(zero, intSort);
    ir_.addAssertion(mkEq(pow2OfZero, one));
    ++axiomCount_;

    // Per-term: for every (pow2 t) found, assert (=> (>= t 0) (>= (pow2 t) 1)).
    // Standard interpretation: pow2(n) = 2^n >= 1 for all n >= 0. Conditional
    // on (>= t 0) so we add no constraint where the argument is negative (the
    // standard interpretation leaves pow2 undefined there; we don't restrict).
    for (ExprId p : sorted) {
        const CoreExpr& pNode = ir_.get(p);
        ExprId arg = pNode.children[0];
        ExprId argGe0  = mkGeq(arg, zero);
        ExprId pow2Ge1 = mkGeq(p, one);
        ir_.addAssertion(mkImplies(argGe0, pow2Ge1));
        ++axiomCount_;
    }
    return true;
}

} // namespace xolver
