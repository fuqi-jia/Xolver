#include "frontend/preprocess/RealDivLowerer.h"

namespace xolver {

RealDivLowerer::RealDivLowerer(CoreIr& ir) : ir_(ir) {}

ExprId RealDivLowerer::rebuildLike(ExprId original,
                                   const std::vector<ExprId>& newChildren) {
    const auto& node = ir_.get(original);
    CoreExpr e;
    e.kind = node.kind;
    e.sort = node.sort;
    e.payload = node.payload;
    for (ExprId c : newChildren) e.children.push_back(c);
    return ir_.add(std::move(e));
}

ExprId RealDivLowerer::mkConstRealZero() {
    CoreExpr e;
    e.kind = Kind::ConstReal;
    e.sort = ir_.realSortId();
    e.payload = Payload(std::string("0"));
    return ir_.add(std::move(e));
}

ExprId RealDivLowerer::mkEq(ExprId a, ExprId b) {
    CoreExpr e;
    e.kind = Kind::Eq;
    e.sort = ir_.boolSortId();
    e.children.push_back(a);
    e.children.push_back(b);
    return ir_.add(std::move(e));
}

ExprId RealDivLowerer::mkNot(ExprId a) {
    CoreExpr e;
    e.kind = Kind::Not;
    e.sort = ir_.boolSortId();
    e.children.push_back(a);
    return ir_.add(std::move(e));
}

ExprId RealDivLowerer::mkImplies(ExprId a, ExprId b) {
    CoreExpr e;
    e.kind = Kind::Implies;
    e.sort = ir_.boolSortId();
    e.children.push_back(a);
    e.children.push_back(b);
    return ir_.add(std::move(e));
}

ExprId RealDivLowerer::mkMul(ExprId a, ExprId b) {
    CoreExpr e;
    e.kind = Kind::Mul;
    e.sort = ir_.realSortId();
    e.children.push_back(a);
    e.children.push_back(b);
    return ir_.add(std::move(e));
}

bool RealDivLowerer::denomNeedsPurify(ExprId eid) const {
    const auto& e = ir_.get(eid);
    // Numeric constants are folded by the PolynomialConverter (poly * 1/c).
    // Everything else (variable / compound) is not a polynomial -> purify.
    return !(e.kind == Kind::ConstInt || e.kind == Kind::ConstReal);
}

ExprId RealDivLowerer::purifyRec(ExprId root) {
    if (auto it = memo_.find(root); it != memo_.end()) return it->second;

    // Iterative post-order (two-visit work-stack); memo_ keyed by ExprId so the
    // first visit of a shared node fixes its purified form. Stack-safe on deep
    // terms (mirrors UfInArithPurifier).
    struct Frame { ExprId e; bool processed; };
    std::vector<Frame> stack;
    stack.push_back({root, false});

    while (!stack.empty()) {
        Frame& frame = stack.back();
        ExprId e = frame.e;
        if (memo_.find(e) != memo_.end()) { stack.pop_back(); continue; }

        const auto node = ir_.get(e);  // value copy: ir_.add() may relocate exprs_

        if (!frame.processed) {
            frame.processed = true;  // do NOT touch `frame` after a push_back
            if (node.isLeaf()) { memo_[e] = e; stack.pop_back(); continue; }
            for (int i = static_cast<int>(node.children.size()) - 1; i >= 0; --i) {
                ExprId c = node.children[i];
                if (memo_.find(c) == memo_.end()) stack.push_back({c, false});
            }
            continue;
        }

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

        // Real division by a non-constant denominator -> fresh q + guarded def.
        const bool isRealDiv = (node.kind == Kind::Div &&
                                node.sort == ir_.realSortId() &&
                                node.children.size() == 2);
        if (isRealDiv && denomNeedsPurify(newChildren[1])) {
            ExprId numer = newChildren[0];
            ExprId denom = newChildren[1];
            ExprId q = ir_.makeFreshVariable(ir_.realSortId(), "divbridge");
            // (=> (not (= denom 0)) (= (* q denom) numer))
            ExprId denomNonzero = mkNot(mkEq(denom, mkConstRealZero()));
            ExprId defConstraint = mkEq(mkMul(q, denom), numer);
            generatedAssertions_.push_back(mkImplies(denomNonzero, defConstraint));
            memo_[e] = q;
            changed_ = true;
        } else {
            memo_[e] = rebuilt;
        }
    }

    return memo_.at(root);
}

bool RealDivLowerer::run() {
    changed_ = false;
    memo_.clear();
    generatedAssertions_.clear();

    auto assertions = ir_.assertions();
    for (ExprId a : assertions) purifyRec(a);

    return changed_;
}

void RealDivLowerer::commit() {
    if (!changed_) return;

    std::vector<ExprId> newAssertions;
    newAssertions.reserve(ir_.assertions().size() + generatedAssertions_.size());
    for (ExprId a : ir_.assertions()) {
        auto it = memo_.find(a);
        newAssertions.push_back(it != memo_.end() ? it->second : a);
    }
    for (ExprId eq : generatedAssertions_) newAssertions.push_back(eq);

    ir_.clearAssertions();
    for (ExprId a : newAssertions) ir_.addAssertion(a);
}

} // namespace xolver
