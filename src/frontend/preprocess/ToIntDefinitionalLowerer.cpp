#include "frontend/preprocess/ToIntDefinitionalLowerer.h"
#include <gmpxx.h>

namespace nlcolver {

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

ExprId ToIntDefinitionalLowerer::rewriteRec(ExprId e, ScopeLevel level) {
    if (auto it = rewriteMemo_.find(e); it != rewriteMemo_.end()) return it->second;

    // Snapshot node because subsequent ir_.add() calls may relocate storage.
    const auto node = ir_.get(e);

    if (node.kind == Kind::ToInt && node.children.size() == 1) {
        // Rewrite child first.
        ExprId arg = rewriteRec(node.children[0], level);
        ExprId i_t = getOrLowerToInt(arg, level);
        rewriteMemo_[e] = i_t;
        didLower_ = true;
        return i_t;
    }

    if (node.kind == Kind::IsInt && node.children.size() == 1) {
        // (is_int t)  <=>  t = to_real(floor(t))
        // i.e. introduce i_t = floor(t) and emit  (= t (to_real i_t)).
        ExprId arg = rewriteRec(node.children[0], level);
        ExprId i_t = getOrLowerToInt(arg, level);
        ExprId toRealI = mkToReal(i_t);
        ExprId eq = mkEq(arg, toRealI);
        rewriteMemo_[e] = eq;
        didLower_ = true;
        return eq;
    }

    if (node.children.empty()) {
        rewriteMemo_[e] = e;
        return e;
    }

    // Recurse into children.
    SmallVector<ExprId, 4> newChildren;
    bool changed = false;
    for (ExprId c : node.children) {
        ExprId rc = rewriteRec(c, level);
        if (rc != c) changed = true;
        newChildren.push_back(rc);
    }
    if (!changed) {
        rewriteMemo_[e] = e;
        return e;
    }
    CoreExpr fresh;
    fresh.kind = node.kind;
    fresh.sort = node.sort;
    fresh.children = std::move(newChildren);
    fresh.payload = node.payload;
    ExprId out = ir_.add(std::move(fresh));
    rewriteMemo_[e] = out;
    return out;
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
    return ir_.add(std::move(e));
}

ExprId ToIntDefinitionalLowerer::mkConstReal(const std::string& s) {
    CoreExpr e;
    e.kind = Kind::ConstReal;
    e.sort = realSortId_;
    e.payload = Payload(s);
    return ir_.add(std::move(e));
}

ExprId ToIntDefinitionalLowerer::mkToReal(ExprId child) {
    CoreExpr e;
    e.kind = Kind::ToReal;
    e.sort = realSortId_;
    e.children.push_back(child);
    return ir_.add(std::move(e));
}

ExprId ToIntDefinitionalLowerer::mkLeq(ExprId a, ExprId b) {
    CoreExpr e;
    e.kind = Kind::Leq;
    e.sort = boolSortId_;
    e.children.push_back(a);
    e.children.push_back(b);
    return ir_.add(std::move(e));
}

ExprId ToIntDefinitionalLowerer::mkLt(ExprId a, ExprId b) {
    CoreExpr e;
    e.kind = Kind::Lt;
    e.sort = boolSortId_;
    e.children.push_back(a);
    e.children.push_back(b);
    return ir_.add(std::move(e));
}

ExprId ToIntDefinitionalLowerer::mkEq(ExprId a, ExprId b) {
    CoreExpr e;
    e.kind = Kind::Eq;
    e.sort = boolSortId_;
    e.children.push_back(a);
    e.children.push_back(b);
    return ir_.add(std::move(e));
}

ExprId ToIntDefinitionalLowerer::mkAdd(ExprId a, ExprId b) {
    CoreExpr e;
    e.kind = Kind::Add;
    e.sort = realSortId_;
    e.children.push_back(a);
    e.children.push_back(b);
    return ir_.add(std::move(e));
}

// ---------------------------------------------------------------------------
// Bridge classification
// ---------------------------------------------------------------------------

bool ToIntDefinitionalLowerer::isNonlinearReal(ExprId e) const {
    // Detects whether the bridge equality `r_t = t` is nonlinear. The check
    // is conservative: any Kind::Mul whose two operands are both non-constant,
    // any Kind::Pow, or any Kind::Div with non-constant divisor counts as
    // nonlinear. Plain variables, ToReal of an Int variable, and linear sums
    // are linear.
    const auto& n = ir_.get(e);
    switch (n.kind) {
        case Kind::ConstInt: case Kind::ConstReal: case Kind::Variable:
            return false;
        case Kind::ToReal:
            return n.children.size() == 1 && isNonlinearReal(n.children[0]);
        case Kind::Neg:
            return n.children.size() == 1 && isNonlinearReal(n.children[0]);
        case Kind::Add:
        case Kind::Sub: {
            for (ExprId c : n.children) if (isNonlinearReal(c)) return true;
            return false;
        }
        case Kind::Mul: {
            if (n.children.size() != 2) return true;  // n-ary mul -> conservative
            const auto& l = ir_.get(n.children[0]);
            const auto& r = ir_.get(n.children[1]);
            bool lConst = (l.kind == Kind::ConstInt || l.kind == Kind::ConstReal);
            bool rConst = (r.kind == Kind::ConstInt || r.kind == Kind::ConstReal);
            if (lConst && !isNonlinearReal(n.children[1])) return false;
            if (rConst && !isNonlinearReal(n.children[0])) return false;
            return true;
        }
        case Kind::Pow:
            return true;
        case Kind::Div: {
            if (n.children.size() != 2) return true;
            const auto& d = ir_.get(n.children[1]);
            bool dConst = (d.kind == Kind::ConstInt || d.kind == Kind::ConstReal);
            if (!dConst) return true;
            return isNonlinearReal(n.children[0]);
        }
        default:
            return true;  // unknown construct -> conservative
    }
}

bool ToIntDefinitionalLowerer::refersToIntVar(ExprId e) const {
    const auto& n = ir_.get(e);
    if (n.kind == Kind::Variable && n.sort == intSortId_) return true;
    for (ExprId c : n.children) {
        if (refersToIntVar(c)) return true;
    }
    return false;
}

bool ToIntDefinitionalLowerer::refersToRealVar(ExprId e) const {
    const auto& n = ir_.get(e);
    if (n.kind == Kind::Variable && n.sort == realSortId_) return true;
    for (ExprId c : n.children) {
        if (refersToRealVar(c)) return true;
    }
    return false;
}

} // namespace nlcolver
