#include "frontend/preprocess/ToIntDefinitionalLowerer.h"
#include <gmpxx.h>

namespace xolver {

ToIntDefinitionalLowerer::ToIntDefinitionalLowerer(CoreIr& ir)
    : ir_(ir),
      boolSortId_(ir.boolSortId()),
      intSortId_(ir.intSortId()),
      realSortId_(ir.realSortId()) {}

bool ToIntDefinitionalLowerer::run() {
    toIntCache_.clear();
    rewriteMemo_.clear();
    lowered_.clear();
    sideAssertions_.clear();
    hadNonlinearBridge_ = false;
    hadIntBridge_ = false;
    hadRealBridge_ = false;
    didLower_ = false;

    for (const auto& [level, eid] : ir_.getScopedAssertions()) {
        ExprId rewritten = rewriteRec(eid, level);
        lowered_.emplace_back(level, rewritten);
    }
    return true;
}

void ToIntDefinitionalLowerer::commit() {
    if (!didLower_) return;
    ir_.clearAssertions();
    for (const auto& [level, eid] : lowered_) {
        ir_.addAssertion(eid, level);
    }
    for (const auto& [level, eid] : sideAssertions_) {
        ir_.addAssertion(eid, level);
    }
}

ExprId ToIntDefinitionalLowerer::rewriteRec(ExprId root, ScopeLevel level) {
    if (auto it = rewriteMemo_.find(root); it != rewriteMemo_.end()) return it->second;

    // Iterative post-order DFS (two-visit work-stack) to avoid stack overflow
    // on deeply nested terms — chains produced by `let`-expansion of program
    // translation benchmarks recurse hundreds of thousands deep. Mirrors
    // ArithCastNormalizer::rewriteRec. A recursive walk here was the panda
    // sweep's ToIntDefinitionalLowerer SIGSEGV (NIA + IDL/LIA/RDL/LRA).
    struct Frame { ExprId e; bool processed; };
    std::vector<Frame> stack;
    stack.push_back({root, false});

    while (!stack.empty()) {
        Frame& frame = stack.back();
        ExprId e = frame.e;

        if (rewriteMemo_.find(e) != rewriteMemo_.end()) {
            stack.pop_back();
            continue;
        }

        // Snapshot by value: getOrLowerToInt()/mk*() below call ir_.addShared(),
        // which may relocate CoreExpr storage and invalidate references.
        const CoreExpr node = ir_.get(e);

        if (!frame.processed) {
            frame.processed = true;  // do NOT touch `frame` after a push_back

            // (to_int t) / (is_int t): rewrite the single argument first, then
            // lower on the second visit.
            if ((node.kind == Kind::ToInt || node.kind == Kind::IsInt) &&
                node.children.size() == 1) {
                ExprId c = node.children[0];
                if (rewriteMemo_.find(c) == rewriteMemo_.end()) {
                    stack.push_back({c, false});
                }
                continue;
            }

            if (node.children.empty()) {
                rewriteMemo_[e] = e;
                stack.pop_back();
                continue;
            }

            // Push children right-to-left so they are processed left-to-right
            // — preserves fresh-variable numbering and side-assertion order.
            for (int i = static_cast<int>(node.children.size()) - 1; i >= 0; --i) {
                ExprId c = node.children[i];
                if (rewriteMemo_.find(c) == rewriteMemo_.end()) {
                    stack.push_back({c, false});
                }
            }
            continue;
        }

        // Second visit: every child is memoized.
        stack.pop_back();

        if (node.kind == Kind::ToInt && node.children.size() == 1) {
            ExprId arg = rewriteMemo_.at(node.children[0]);
            ExprId i_t = getOrLowerToInt(arg, level);
            rewriteMemo_[e] = i_t;
            didLower_ = true;
            continue;
        }

        if (node.kind == Kind::IsInt && node.children.size() == 1) {
            // (is_int t)  <=>  t = to_real(floor(t))
            ExprId arg = rewriteMemo_.at(node.children[0]);
            ExprId i_t = getOrLowerToInt(arg, level);
            ExprId toRealI = mkToReal(i_t);
            ExprId eq = mkEq(arg, toRealI);
            rewriteMemo_[e] = eq;
            didLower_ = true;
            continue;
        }

        SmallVector<ExprId, 4> newChildren;
        bool changed = false;
        for (ExprId c : node.children) {
            ExprId rc = rewriteMemo_.at(c);
            if (rc != c) changed = true;
            newChildren.push_back(rc);
        }
        if (!changed) {
            rewriteMemo_[e] = e;
        } else {
            CoreExpr fresh;
            fresh.kind = node.kind;
            fresh.sort = node.sort;
            fresh.children = std::move(newChildren);
            fresh.payload = node.payload;
            rewriteMemo_[e] = ir_.addShared(std::move(fresh));
        }
    }

    return rewriteMemo_.at(root);
}

ExprId ToIntDefinitionalLowerer::getOrLowerToInt(ExprId arg, ScopeLevel level) {
    Key key{arg, level};
    if (auto it = toIntCache_.find(key); it != toIntCache_.end()) return it->second;

    // Argument may be Int-sorted (degenerate case: to_int over an Int term is
    // the identity). Detect and short-circuit.
    const SortId argSort = ir_.get(arg).sort;
    if (argSort == intSortId_) {
        // Argument is already an Int term; semantically `to_int` is the identity.
        // Bridge equalities are unnecessary; just memoize and return.
        toIntCache_[key] = arg;
        return arg;
    }

    ExprId i_t = ir_.makeFreshVariable(intSortId_, "__nlc_floor");
    // r_t is a fresh Real proxy for the original argument; the bridge
    // equality routes through the atomizer to whichever arithmetic theory
    // owns the original expression.
    ExprId r_t = ir_.makeFreshVariable(realSortId_, "__nlc_floor_r");

    // Soundness side-effects: track what kind of bridge we are introducing
    // so the Solver can upgrade the declared logic.
    if (isNonlinearReal(arg)) hadNonlinearBridge_ = true;
    if (refersToIntVar(arg)) hadIntBridge_ = true;
    if (refersToRealVar(arg)) hadRealBridge_ = true;

    // (= r_t t)
    sideAssertions_.emplace_back(level, mkEq(r_t, arg));
    // (<= (to_real i_t) r_t)
    ExprId toRealI = mkToReal(i_t);
    sideAssertions_.emplace_back(level, mkLeq(toRealI, r_t));
    // (<  r_t (+ (to_real i_t) 1))
    ExprId one = mkConstReal("1");
    ExprId iPlusOne = mkAdd(toRealI, one);
    sideAssertions_.emplace_back(level, mkLt(r_t, iPlusOne));

    toIntCache_[key] = i_t;
    return i_t;
}

// ---------------------------------------------------------------------------
// IR builders
// ---------------------------------------------------------------------------

ExprId ToIntDefinitionalLowerer::mkConstInt(int64_t v) {
    CoreExpr e;
    e.kind = Kind::ConstInt;
    e.sort = intSortId_;
    e.payload = Payload(v);
    return ir_.addShared(std::move(e));
}

ExprId ToIntDefinitionalLowerer::mkConstReal(const std::string& s) {
    CoreExpr e;
    e.kind = Kind::ConstReal;
    e.sort = realSortId_;
    e.payload = Payload(s);
    return ir_.addShared(std::move(e));
}

ExprId ToIntDefinitionalLowerer::mkToReal(ExprId child) {
    CoreExpr e;
    e.kind = Kind::ToReal;
    e.sort = realSortId_;
    e.children.push_back(child);
    return ir_.addShared(std::move(e));
}

ExprId ToIntDefinitionalLowerer::mkLeq(ExprId a, ExprId b) {
    CoreExpr e;
    e.kind = Kind::Leq;
    e.sort = boolSortId_;
    e.children.push_back(a);
    e.children.push_back(b);
    return ir_.addShared(std::move(e));
}

ExprId ToIntDefinitionalLowerer::mkLt(ExprId a, ExprId b) {
    CoreExpr e;
    e.kind = Kind::Lt;
    e.sort = boolSortId_;
    e.children.push_back(a);
    e.children.push_back(b);
    return ir_.addShared(std::move(e));
}

ExprId ToIntDefinitionalLowerer::mkEq(ExprId a, ExprId b) {
    CoreExpr e;
    e.kind = Kind::Eq;
    e.sort = boolSortId_;
    e.children.push_back(a);
    e.children.push_back(b);
    return ir_.addShared(std::move(e));
}

ExprId ToIntDefinitionalLowerer::mkAdd(ExprId a, ExprId b) {
    CoreExpr e;
    e.kind = Kind::Add;
    e.sort = realSortId_;
    e.children.push_back(a);
    e.children.push_back(b);
    return ir_.addShared(std::move(e));
}

// ---------------------------------------------------------------------------
// Bridge classification
// ---------------------------------------------------------------------------

bool ToIntDefinitionalLowerer::isNonlinearReal(ExprId root) const {
    // Detects whether the bridge equality `r_t = t` is nonlinear. The check
    // is conservative: any Kind::Mul whose two operands are both non-constant,
    // any Kind::Pow, or any Kind::Div with non-constant divisor counts as
    // nonlinear. Plain variables, ToReal of an Int variable, and linear sums
    // are linear. Iterative (explicit worklist) to avoid stack overflow on
    // deeply nested arguments; a pure predicate, so visitation order is
    // irrelevant to the result. Mul/Div "recurse into the single non-constant
    // operand" becomes "push that operand".
    std::vector<ExprId> stack{root};
    while (!stack.empty()) {
        ExprId e = stack.back();
        stack.pop_back();
        const auto& n = ir_.get(e);
        switch (n.kind) {
            case Kind::ConstInt: case Kind::ConstReal: case Kind::Variable:
                break;  // linear contribution
            case Kind::ToReal:
            case Kind::Neg:
                // Original: `size==1 && isNonlinearReal(child)` — malformed
                // arity is treated as linear (false), not conservative.
                if (n.children.size() == 1) stack.push_back(n.children[0]);
                break;
            case Kind::Add:
            case Kind::Sub:
                for (ExprId c : n.children) stack.push_back(c);
                break;
            case Kind::Mul: {
                if (n.children.size() != 2) return true;  // n-ary mul -> conservative
                const auto& l = ir_.get(n.children[0]);
                const auto& r = ir_.get(n.children[1]);
                bool lConst = (l.kind == Kind::ConstInt || l.kind == Kind::ConstReal);
                bool rConst = (r.kind == Kind::ConstInt || r.kind == Kind::ConstReal);
                if (!lConst && !rConst) return true;  // non-const * non-const
                // exactly one constant: nonlinear iff the other operand is
                stack.push_back(lConst ? n.children[1] : n.children[0]);
                break;
            }
            case Kind::Pow:
                return true;
            case Kind::Div: {
                if (n.children.size() != 2) return true;
                const auto& d = ir_.get(n.children[1]);
                bool dConst = (d.kind == Kind::ConstInt || d.kind == Kind::ConstReal);
                if (!dConst) return true;
                stack.push_back(n.children[0]);
                break;
            }
            default:
                return true;  // unknown construct -> conservative
        }
    }
    return false;
}

bool ToIntDefinitionalLowerer::refersToIntVar(ExprId root) const {
    std::vector<ExprId> stack{root};
    while (!stack.empty()) {
        const auto& n = ir_.get(stack.back());
        stack.pop_back();
        if (n.kind == Kind::Variable && n.sort == intSortId_) return true;
        for (ExprId c : n.children) stack.push_back(c);
    }
    return false;
}

bool ToIntDefinitionalLowerer::refersToRealVar(ExprId root) const {
    std::vector<ExprId> stack{root};
    while (!stack.empty()) {
        const auto& n = ir_.get(stack.back());
        stack.pop_back();
        if (n.kind == Kind::Variable && n.sort == realSortId_) return true;
        for (ExprId c : n.children) stack.push_back(c);
    }
    return false;
}

} // namespace xolver
