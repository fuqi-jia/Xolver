#include "frontend/preprocess/BoolSubtermPurifier.h"
#include <cassert>
#include <iostream>

namespace zolver {

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

// True iff child position @p i of a node of kind @p k is an "atomic bool
// position" — a place where a bool composite is allowed without purification.
// Index-correct (no fixed 4-cap), so n-ary And/Or with >4 children behave
// like the first four rather than reading past a fixed array (former UB).
static bool isAtomicBoolPos(Kind k, size_t i) {
    switch (k) {
        case Kind::Not:     return i == 0;
        case Kind::And:
        case Kind::Or:
        case Kind::Implies:
        case Kind::Xor:     return true;        // every operand is a bool position
        case Kind::Ite:     return i == 0;      // only the condition
        default:            return false;
    }
}

ExprId BoolSubtermPurifier::purifyRec(ExprId root, bool rootInArgPosition) {
    if (auto it = memo_.find(root); it != memo_.end()) return it->second;

    // Iterative post-order (two-visit work-stack) carrying the per-node
    // inArgPosition flag in the frame. memo_ is keyed by ExprId only, so the
    // first DFS visit of a shared node fixes its purified form — matching the
    // former left-to-right recursion. Stack-safe at any depth, so the previous
    // kMaxRecursionDepth bail-out (which silently skipped purification on deep
    // terms) is no longer needed.
    struct Frame { ExprId e; bool inArgPosition; bool processed; };
    std::vector<Frame> stack;
    stack.push_back({root, rootInArgPosition, false});

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
                if (memo_.find(c) == memo_.end()) {
                    bool childInArg = frame.inArgPosition ||
                                      !isAtomicBoolPos(node.kind, static_cast<size_t>(i));
                    stack.push_back({c, childInArg, false});
                }
            }
            continue;
        }

        const bool inArgPosition = frame.inArgPosition;
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

        // If this expression sits in an argument position and is a bool
        // composite, replace it with a fresh variable + equivalence constraint.
        if (inArgPosition && isBoolComposite(rebuilt)) {
            // Capture fields BEFORE makeFreshVariable()/mk*() call ir_.add()
            // (which may relocate exprs_ and dangle any reference).
            const Kind rebuiltKind = ir_.get(rebuilt).kind;
            ExprId notChild = NullExpr;
            if (rebuiltKind == Kind::Not && ir_.get(rebuilt).children.size() == 1) {
                notChild = ir_.get(rebuilt).children[0];
            }

            ExprId fresh = ir_.makeFreshVariable(boolSortId_, "boolpur");
            if (notChild != NullExpr) {
                // Not(a) in Bool ≡ a != fresh, which EUF handles as a disequality.
                generatedAssertions_.push_back(mkDistinct(fresh, notChild));
            } else {
                generatedAssertions_.push_back(mkEq(fresh, rebuilt));
            }
            memo_[e] = fresh;
            changed_ = true;
        } else {
            memo_[e] = rebuilt;
        }
    }

    return memo_.at(root);
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
        newAssertions.push_back(purifyRec(a, false));
    }
    ir_.replaceAssertions(newAssertions);

    return changed_;
}

void BoolSubtermPurifier::commit() {
    for (ExprId a : generatedAssertions_) {
        ir_.addAssertion(a);
    }
}

} // namespace zolver
