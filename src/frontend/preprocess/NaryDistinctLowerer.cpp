#include "frontend/preprocess/NaryDistinctLowerer.h"
#include <cassert>

namespace nlcolver {

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

ExprId NaryDistinctLowerer::lowerRec(ExprId e) {
    if (auto it = memo_.find(e); it != memo_.end()) {
        return it->second;
    }

    const auto node = ir_.get(e);

    // Rebuild children first (post-order)
    std::vector<ExprId> newChildren;
    newChildren.reserve(node.children.size());
    bool changed = false;
    for (ExprId c : node.children) {
        ExprId lc = lowerRec(c);
        if (lc != c) changed = true;
        newChildren.push_back(lc);
    }

    // Handle n-ary distinct: lower to pairwise binary distinct using lowered children
    if (node.kind == Kind::Distinct && newChildren.size() > 2) {
        ExprId result = lowerDistinct(newChildren);
        memo_[e] = result;
        return result;
    }

    // If no child changed and not n-ary distinct, keep original
    if (!changed) {
        memo_[e] = e;
        return e;
    }

    // Rebuild node with lowered children
    CoreExpr ne;
    ne.kind = node.kind;
    ne.sort = node.sort;
    for (ExprId c : newChildren) ne.children.push_back(c);
    ne.payload = node.payload;
    ExprId rebuilt = ir_.add(std::move(ne));
    memo_[e] = rebuilt;
    return rebuilt;
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
    return ir_.add(std::move(e));
}

ExprId NaryDistinctLowerer::mkAnd(ExprId a, ExprId b) {
    CoreExpr e;
    e.kind = Kind::And;
    e.sort = boolSortId_;
    e.children.push_back(a);
    e.children.push_back(b);
    return ir_.add(std::move(e));
}

ExprId NaryDistinctLowerer::mkTrue() {
    CoreExpr e;
    e.kind = Kind::ConstBool;
    e.sort = boolSortId_;
    e.payload = Payload(true);
    return ir_.add(std::move(e));
}

} // namespace nlcolver
