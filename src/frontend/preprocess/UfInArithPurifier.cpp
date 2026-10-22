#include "frontend/preprocess/UfInArithPurifier.h"
#include <cassert>

namespace xolver {

UfInArithPurifier::UfInArithPurifier(NativeTerms& ir) : ir_(ir) {}

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
        case Kind::IsInt:
        case Kind::Lt:
        case Kind::Leq:
        case Kind::Gt:
        case Kind::Geq:
            return true;
        default:
            return false;
    }
}

bool UfInArithPurifier::isArithPosition(const TermExpr& node, size_t child) const {
    if (isArithKind(node.kind)) return true;
    if (node.kind == Kind::Eq || node.kind == Kind::Distinct ||
        (node.kind == Kind::Ite && child > 0)) {
        // Comparisons themselves have Boolean sort; their operand sorts decide
        // whether the application crosses into arithmetic.
        const auto sort = ir_.sortKind(ir_.get(node.children[child]).sort);
        return sort == SortKind::Int || sort == SortKind::Real;
    }
    return false;
}

ExprId UfInArithPurifier::rebuildLike(ExprId original,
                                       const std::vector<ExprId>& newChildren) {
    const auto& node = ir_.get(original);
    TermExpr e;
    e.kind = node.kind;
    e.sort = node.sort;
    e.payload = node.payload;
    for (ExprId c : newChildren) {
        e.children.push_back(c);
    }
    return ir_.addShared(std::move(e));
}

ExprId UfInArithPurifier::mkEq(ExprId a, ExprId b) {
    TermExpr e;
    e.kind = Kind::Eq;
    e.sort = ir_.boolSortId();
    e.children.push_back(a);
    e.children.push_back(b);
    return ir_.addShared(std::move(e));
}

ExprId UfInArithPurifier::purifyRec(ExprId root, bool rootInArithContext) {
    if (auto it = memo_.find(memoKey(root, rootInArithContext)); it != memo_.end())
        return it->second;

    // Iterative post-order (two-visit work-stack) carrying the per-node
    // arithmetic-context flag. A shared node can be retained as a UF argument
    // and bridged as an arithmetic operand, independently of visitation order.
    struct Frame { ExprId e; bool inArithContext; bool processed; };
    std::vector<Frame> stack;
    stack.push_back({root, rootInArithContext, false});

    while (!stack.empty()) {
        Frame& frame = stack.back();
        ExprId e = frame.e;
        const bool inArithContext = frame.inArithContext;
        const auto key = memoKey(e, inArithContext);
        if (memo_.find(key) != memo_.end()) { stack.pop_back(); continue; }

        const auto node = ir_.get(e);

        if (!frame.processed) {
            frame.processed = true;  // do NOT touch `frame` after a push_back

            if (node.isLeaf()) { memo_[key] = e; stack.pop_back(); continue; }

            for (int i = static_cast<int>(node.children.size()) - 1; i >= 0; --i) {
                ExprId c = node.children[i];
                const bool ctx = isArithPosition(node, static_cast<size_t>(i));
                if (memo_.find(memoKey(c, ctx)) == memo_.end()) {
                    stack.push_back({c, ctx, false});
                }
            }
            continue;
        }

        stack.pop_back();

        std::vector<ExprId> newChildren;
        newChildren.reserve(node.children.size());
        bool childrenChanged = false;
        for (size_t i = 0; i < node.children.size(); ++i) {
            const auto c = node.children[i];
            ExprId rc = memo_.at(memoKey(c, isArithPosition(node, i)));
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
            memo_[key] = fresh;
            changed_ = true;
        } else {
            memo_[key] = rebuilt;
        }
    }

    return memo_.at(memoKey(root, rootInArithContext));
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
        auto it = memo_.find(memoKey(a, false));
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
