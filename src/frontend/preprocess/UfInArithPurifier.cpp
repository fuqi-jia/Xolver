#include "frontend/preprocess/UfInArithPurifier.h"
#include <cassert>

namespace nlcolver {

UfInArithPurifier::UfInArithPurifier(CoreIr& ir) : ir_(ir) {}

bool UfInArithPurifier::isArithKind(Kind k) {
    switch (k) {
        case Kind::Add:
        case Kind::Sub:
        case Kind::Neg:
        case Kind::Mul:
        case Kind::Div:
        case Kind::Mod:
        case Kind::Abs:
        case Kind::Pow:
        case Kind::ToInt:
        case Kind::ToReal:
        case Kind::Lt:
        case Kind::Leq:
        case Kind::Gt:
        case Kind::Geq:
            return true;
        default:
            return false;
    }
}

ExprId UfInArithPurifier::rebuildLike(ExprId original,
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

ExprId UfInArithPurifier::mkEq(ExprId a, ExprId b) {
    CoreExpr e;
    e.kind = Kind::Eq;
    e.sort = ir_.boolSortId();
    e.children.push_back(a);
    e.children.push_back(b);
    return ir_.add(std::move(e));
}

ExprId UfInArithPurifier::purifyRec(ExprId e, bool inArithContext) {
    auto it = memo_.find(e);
    if (it != memo_.end()) {
        return it->second;
    }

    const auto& node = ir_.get(e);

    // Leaf nodes: nothing to do
    if (node.isLeaf()) {
        memo_[e] = e;
        return e;
    }

    // Determine which child positions are arithmetic contexts
    bool childInArith[4] = {false, false, false, false};
    if (isArithKind(node.kind)) {
        for (size_t i = 0; i < node.children.size() && i < 4; ++i) {
            childInArith[i] = true;
        }
    } else if (node.kind == Kind::Eq) {
        // Eq is an arithmetic context if the arguments are Int or Real
        if (node.sort == ir_.intSortId() || node.sort == ir_.realSortId()) {
            for (size_t i = 0; i < node.children.size() && i < 4; ++i) {
                childInArith[i] = true;
            }
        }
    } else if (node.kind == Kind::Distinct) {
        // Distinct over Int/Real args is also an arithmetic context
        if (node.sort == ir_.intSortId() || node.sort == ir_.realSortId()) {
            for (size_t i = 0; i < node.children.size() && i < 4; ++i) {
                childInArith[i] = true;
            }
        }
    }

    // Recursively process children
    std::vector<ExprId> newChildren;
    newChildren.reserve(node.children.size());
    for (size_t i = 0; i < node.children.size(); ++i) {
        newChildren.push_back(purifyRec(node.children[i], childInArith[i]));
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

    // If this expression is a UFApply in an arithmetic context, bridge it
    if (node.kind == Kind::UFApply && inArithContext) {
        ExprId fresh = ir_.makeFreshVariable(node.sort, "ufbridge");
        ExprId eq = mkEq(fresh, rebuilt);
        generatedAssertions_.push_back(eq);
        memo_[e] = fresh;
        changed_ = true;
        return fresh;
    }

    memo_[e] = rebuilt;
    return rebuilt;
}

bool UfInArithPurifier::run() {
    changed_ = false;
    memo_.clear();
    generatedAssertions_.clear();

    // Process all existing assertions
    auto assertions = ir_.assertions();
    for (ExprId a : assertions) {
        purifyRec(a, false);
    }

    return changed_;
}

void UfInArithPurifier::commit() {
    if (!changed_) return;

    // Replace original assertions with purified versions
    std::vector<ExprId> newAssertions;
    newAssertions.reserve(ir_.assertions().size() + generatedAssertions_.size());

    for (ExprId a : ir_.assertions()) {
        auto it = memo_.find(a);
        if (it != memo_.end()) {
            newAssertions.push_back(it->second);
        } else {
            newAssertions.push_back(a);
        }
    }

    // Add bridge equalities
    for (ExprId eq : generatedAssertions_) {
        newAssertions.push_back(eq);
    }

    // Debug removed

    ir_.clearAssertions();
    for (ExprId a : newAssertions) {
        ir_.addAssertion(a);
    }
}

} // namespace nlcolver
