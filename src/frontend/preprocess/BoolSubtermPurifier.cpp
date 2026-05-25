#include "frontend/preprocess/BoolSubtermPurifier.h"
#include <cassert>
#include <iostream>

namespace nlcolver {

BoolSubtermPurifier::BoolSubtermPurifier(CoreIr& ir)
    : ir_(ir), boolSortId_(ir.boolSortId()) {}

bool BoolSubtermPurifier::isBoolComposite(ExprId e) const {
    const auto& node = ir_.get(e);
    // Use sortKind as fallback if boolSortId_ is not set
    bool isBoolSort = (node.sort == boolSortId_);
    if (!isBoolSort && boolSortId_ == NullSort) {
        if (auto sk = ir_.sortKind(node.sort); sk && *sk == SortKind::Bool) {
            isBoolSort = true;
        }
    }
    if (!isBoolSort) return false;
    switch (node.kind) {
        case Kind::Not:
        case Kind::And:
        case Kind::Or:
        case Kind::Implies:
        case Kind::Xor:
        case Kind::Ite:
            return true;
        default:
            return false;
    }
}

ExprId BoolSubtermPurifier::rebuildLike(ExprId original,
                                         const std::vector<ExprId>& newChildren) {
    const auto& node = ir_.get(original);
    CoreExpr e;
    e.kind = node.kind;
    e.sort = node.sort;
    e.payload = node.payload;
    for (ExprId c : newChildren) {
        e.children.push_back(c);
    }
    return ir_.add(std::move(e));
}

ExprId BoolSubtermPurifier::mkEq(ExprId a, ExprId b) {
    CoreExpr e;
    e.kind = Kind::Eq;
    e.sort = boolSortId_;
    e.children.push_back(a);
    e.children.push_back(b);
    return ir_.add(std::move(e));
}

ExprId BoolSubtermPurifier::mkAnd(ExprId a, ExprId b) {
    CoreExpr e;
    e.kind = Kind::And;
    e.sort = boolSortId_;
    e.children.push_back(a);
    e.children.push_back(b);
    return ir_.add(std::move(e));
}

ExprId BoolSubtermPurifier::mkOr(ExprId a, ExprId b) {
    CoreExpr e;
    e.kind = Kind::Or;
    e.sort = boolSortId_;
    e.children.push_back(a);
    e.children.push_back(b);
    return ir_.add(std::move(e));
}

ExprId BoolSubtermPurifier::mkImplies(ExprId a, ExprId b) {
    CoreExpr e;
    e.kind = Kind::Implies;
    e.sort = boolSortId_;
    e.children.push_back(a);
    e.children.push_back(b);
    return ir_.add(std::move(e));
}

ExprId BoolSubtermPurifier::mkNot(ExprId a) {
    CoreExpr e;
    e.kind = Kind::Not;
    e.sort = boolSortId_;
    e.children.push_back(a);
    return ir_.add(std::move(e));
}

ExprId BoolSubtermPurifier::mkDistinct(ExprId a, ExprId b) {
    CoreExpr e;
    e.kind = Kind::Distinct;
    e.sort = boolSortId_;
    e.children.push_back(a);
    e.children.push_back(b);
    return ir_.add(std::move(e));
}

ExprId BoolSubtermPurifier::purifyRec(ExprId e, bool inArgPosition, int depth) {
    auto it = memo_.find(e);
    if (it != memo_.end()) {
        return it->second;
    }

    // Defensive: deep expressions (e.g. Dartagnan nested arrays) can exhaust
    // the C++ call stack (>29K frames observed).  Beyond the safe depth cap
    // we return the expression unchanged: any bool-composite this deep would
    // blow up the SAT encoding anyway, and the typical deep cases are
    // non-bool nodes (Select/Store chains) that need no purification.
    if (depth > kMaxRecursionDepth) {
        memo_[e] = e;
        return e;
    }

    // Value copy: ir_.add() may reallocate exprs_, invalidating references.
    const auto node = ir_.get(e);

    // Leaf nodes: nothing to do
    if (node.isLeaf()) {
        memo_[e] = e;
        return e;
    }

    // Determine which child positions are "atomic bool positions"
    // (i.e. standard places where bool composites are allowed without purification)
    bool childIsAtomicBoolPos[4] = {false, false, false, false};
    switch (node.kind) {
        case Kind::Not:
            if (node.children.size() >= 1) childIsAtomicBoolPos[0] = true;
            break;
        case Kind::And:
        case Kind::Or:
        case Kind::Implies:
        case Kind::Xor:
            for (size_t i = 0; i < node.children.size() && i < 4; ++i)
                childIsAtomicBoolPos[i] = true;
            break;
        case Kind::Ite:
            if (node.children.size() >= 1) childIsAtomicBoolPos[0] = true;
            break;
        default:
            break;
    }

    // Recursively process children
    std::vector<ExprId> newChildren;
    newChildren.reserve(node.children.size());
    for (size_t i = 0; i < node.children.size(); ++i) {
        bool childInArg = inArgPosition || !childIsAtomicBoolPos[i];
        newChildren.push_back(purifyRec(node.children[i], childInArg, depth + 1));
    }

    ExprId rebuilt = e;
    bool childrenChanged = false;
    for (size_t i = 0; i < node.children.size(); ++i) {
        if (newChildren[i] != node.children[i]) {
            childrenChanged = true;
            break;
        }
    }
    if (childrenChanged) {
        rebuilt = rebuildLike(e, newChildren);
        changed_ = true;
    }

    // If this expression itself sits in an argument position and is a bool composite,
    // replace it with a fresh variable and emit an equivalence constraint.
    if (inArgPosition && isBoolComposite(rebuilt)) {
        const auto& rebuiltNode = ir_.get(rebuilt);

        // Special case: Not(a) in Bool is equivalent to a != fresh,
        // which EUF can handle as a disequality.
        if (rebuiltNode.kind == Kind::Not && rebuiltNode.children.size() == 1) {
            ExprId fresh = ir_.makeFreshVariable(boolSortId_, "boolpur");
            ExprId distinct = mkDistinct(fresh, rebuiltNode.children[0]);
            generatedAssertions_.push_back(distinct);
            memo_[e] = fresh;
            changed_ = true;
            return fresh;
        }

        ExprId fresh = ir_.makeFreshVariable(boolSortId_, "boolpur");

        // Encode  fresh ↔ rebuilt
        // For bool sorts, equality is sufficient:  fresh = rebuilt
        ExprId eq = mkEq(fresh, rebuilt);
        generatedAssertions_.push_back(eq);

        memo_[e] = fresh;
        changed_ = true;
        return fresh;
    }

    memo_[e] = rebuilt;
    return rebuilt;
}

bool BoolSubtermPurifier::run() {
    changed_ = false;
    memo_.clear();
    generatedAssertions_.clear();

    // Process all current assertions at scope 0 (they are in formula position)
    auto assertions = ir_.assertions();
    std::vector<ExprId> newAssertions;
    newAssertions.reserve(assertions.size());
    for (ExprId a : assertions) {
        newAssertions.push_back(purifyRec(a, false, 0));
    }
    ir_.replaceAssertions(newAssertions);

    return changed_;
}

void BoolSubtermPurifier::commit() {
    for (ExprId a : generatedAssertions_) {
        ir_.addAssertion(a);
    }
}

} // namespace nlcolver
