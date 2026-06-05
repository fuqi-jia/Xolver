#include "frontend/preprocess/NaryDistinctLowerer.h"
#include <cassert>

namespace xolver {

NaryDistinctLowerer::NaryDistinctLowerer(CoreIr& ir)
    : ir_(ir), boolSortId_(ir.boolSortId()) {
}

bool NaryDistinctLowerer::run() {
    memo_.clear();
    loweredAssertions_.clear();

    auto scoped = ir_.getScopedAssertions();
    for (const auto& [level, a] : scoped) {
        memo_.clear();
        ExprId lowered = lowerRec(a);
        loweredAssertions_.push_back({level, lowered});
    }
    return true;
}

void NaryDistinctLowerer::commit() {
    ir_.clearAssertions();
    for (const auto& [level, e] : loweredAssertions_) {
        ir_.addAssertion(e, level);
    }
}

ExprId NaryDistinctLowerer::lowerRec(ExprId root) {
    if (auto it = memo_.find(root); it != memo_.end()) return it->second;

    // Iterative post-order (two-visit work-stack) to avoid stack overflow on
    // deeply nested terms. Behavior-identical to the former recursion.
    struct Frame { ExprId e; bool processed; };
    std::vector<Frame> stack;
    stack.push_back({root, false});

    while (!stack.empty()) {
        Frame& frame = stack.back();
        ExprId e = frame.e;
        if (memo_.find(e) != memo_.end()) { stack.pop_back(); continue; }

        const auto node = ir_.get(e);  // value copy: ir_.addShared() may relocate exprs_

        if (!frame.processed) {
            frame.processed = true;
            if (node.children.empty()) { memo_[e] = e; stack.pop_back(); continue; }
            for (int i = static_cast<int>(node.children.size()) - 1; i >= 0; --i) {
                ExprId c = node.children[i];
                if (memo_.find(c) == memo_.end()) stack.push_back({c, false});
            }
            continue;
        }

        stack.pop_back();
        std::vector<ExprId> newChildren;
        newChildren.reserve(node.children.size());
        bool changed = false;
        for (ExprId c : node.children) {
            ExprId lc = memo_.at(c);
            if (lc != c) changed = true;
            newChildren.push_back(lc);
        }

        // n-ary distinct -> pairwise binary distinct using lowered children.
        if (node.kind == Kind::Distinct && newChildren.size() > 2) {
            memo_[e] = lowerDistinct(newChildren);
        } else if (!changed) {
            memo_[e] = e;
        } else {
            CoreExpr ne;
            ne.kind = node.kind;
            ne.sort = node.sort;
            for (ExprId c : newChildren) ne.children.push_back(c);
            ne.payload = node.payload;
            memo_[e] = ir_.addShared(std::move(ne));
        }
    }

    return memo_.at(root);
}

ExprId NaryDistinctLowerer::lowerDistinct(const std::vector<ExprId>& children) {
    assert(children.size() > 2);
    size_t n = children.size();

    // Build pairwise distincts: and( distinct(c0,c1), distinct(c0,c2), ... )
    ExprId result = mkTrue();
    for (size_t i = 0; i < n; ++i) {
        for (size_t j = i + 1; j < n; ++j) {
            ExprId pair = mkDistinct(children[i], children[j]);
            result = mkAnd(result, pair);
        }
    }
    return result;
}

ExprId NaryDistinctLowerer::mkDistinct(ExprId a, ExprId b) {
    CoreExpr e;
    e.kind = Kind::Distinct;
    e.sort = boolSortId_;
    e.children.push_back(a);
    e.children.push_back(b);
    return ir_.addShared(std::move(e));
}

ExprId NaryDistinctLowerer::mkAnd(ExprId a, ExprId b) {
    CoreExpr e;
    e.kind = Kind::And;
    e.sort = boolSortId_;
    e.children.push_back(a);
    e.children.push_back(b);
    return ir_.addShared(std::move(e));
}

ExprId NaryDistinctLowerer::mkTrue() {
    CoreExpr e;
    e.kind = Kind::ConstBool;
    e.sort = boolSortId_;
    e.payload = Payload(true);
    return ir_.addShared(std::move(e));
}

} // namespace xolver
