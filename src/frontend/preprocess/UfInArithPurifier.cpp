#include "frontend/preprocess/UfInArithPurifier.h"
#include <cassert>

namespace xolver {

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

ExprId UfInArithPurifier::purifyRec(ExprId root, bool rootInArithContext) {
    if (auto it = memo_.find(root); it != memo_.end()) return it->second;

    // Iterative post-order (two-visit work-stack) carrying the per-node
    // arithmetic-context flag in the frame. memo_ is keyed by ExprId only, so
    // the first DFS visit of a shared node fixes its purified form — exactly
    // matching the former left-to-right recursion. Stack-safe on deep terms.
    struct Frame { ExprId e; bool inArithContext; bool processed; };
    std::vector<Frame> stack;
    stack.push_back({root, rootInArithContext, false});

    while (!stack.empty()) {
        Frame& frame = stack.back();
        ExprId e = frame.e;
        if (memo_.find(e) != memo_.end()) { stack.pop_back(); continue; }

        const auto node = ir_.get(e);  // value copy: ir_.add() may relocate exprs_

        if (!frame.processed) {
            frame.processed = true;  // do NOT touch `frame` after a push_back

            if (node.isLeaf()) { memo_[e] = e; stack.pop_back(); continue; }

            // Which child positions are arithmetic contexts.
            bool childInArith[4] = {false, false, false, false};
            const bool arithNode =
                isArithKind(node.kind) ||
                ((node.kind == Kind::Eq || node.kind == Kind::Distinct) &&
                 (node.sort == ir_.intSortId() || node.sort == ir_.realSortId()));
            if (arithNode) {
                for (size_t i = 0; i < node.children.size() && i < 4; ++i) childInArith[i] = true;
            }

            for (int i = static_cast<int>(node.children.size()) - 1; i >= 0; --i) {
                ExprId c = node.children[i];
                if (memo_.find(c) == memo_.end()) {
                    bool ctx = (i < 4) ? childInArith[i] : false;
                    stack.push_back({c, ctx, false});
                }
            }
            continue;
        }

        const bool inArithContext = frame.inArithContext;
        stack.pop_back();

        std::vector<ExprId> newChildren;
        newChildren.reserve(node.children.size());
        bool childrenChanged = false;
        for (ExprId c : node.children) {
            ExprId rc = memo_.at(c);
            if (rc != c) childrenChanged = true;
            newChildren.push_back(rc);
        }

        ExprId rebuilt = e;
        if (childrenChanged) {
            rebuilt = rebuildLike(e, newChildren);
            changed_ = true;
        }

        if (node.kind == Kind::UFApply && inArithContext) {
            ExprId fresh = ir_.makeFreshVariable(node.sort, "ufbridge");
            ExprId eq = mkEq(fresh, rebuilt);
            generatedAssertions_.push_back(eq);
            memo_[e] = fresh;
            changed_ = true;
        } else {
            memo_[e] = rebuilt;
        }
    }

    return memo_.at(root);
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

} // namespace xolver
