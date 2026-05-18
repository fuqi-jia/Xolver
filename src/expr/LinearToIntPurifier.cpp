#include "expr/LinearToIntPurifier.h"
#include <gmpxx.h>

namespace nlcolver {

// ---------------------------------------------------------------------------
// Phase 1: detect-only
// ---------------------------------------------------------------------------

ToIntDetectResult LinearToIntPurifier::detectOnly() const {
    ToIntDetectResult result;
    for (const auto& [level, a] : ir_.getScopedAssertions()) {
        (void)level;
        if (hasUnsupportedToInt(a)) {
            result.hasUnsupportedNonlinearToInt = true;
            return result;
        }
    }
    return result;
}

bool LinearToIntPurifier::hasUnsupportedToInt(ExprId e) const {
    const auto& node = ir_.get(e);
    if (node.kind == Kind::ToInt && node.children.size() == 1) {
        if (!isLinearRealExpr(node.children[0])) return true;
    }
    for (ExprId c : node.children) {
        if (hasUnsupportedToInt(c)) return true;
    }
    return false;
}

// ---------------------------------------------------------------------------
// Phase 2: purification
// ---------------------------------------------------------------------------

ToIntPurifyResult LinearToIntPurifier::run() {
    ToIntPurifyResult result;
    for (const auto& [level, a] : ir_.getScopedAssertions()) {
        result.purifiedAssertions.push_back({level, purifyRec(a, level)});
    }

    for (const auto& info : infos_) {
        ExprId lower = makeFloorLowerLemma(info.freshIntVar, info.realArg);
        ExprId upper = makeFloorUpperLemma(info.freshIntVar, info.realArg);
        result.floorLemmas.push_back({info.level, lower});
        result.floorLemmas.push_back({info.level, upper});
    }

    result.infos = std::move(infos_);
    result.hasUnsupportedNonlinearToInt = hasUnsupportedNonlinearToInt_;
    return result;
}

ExprId LinearToIntPurifier::purifyRec(ExprId e, ScopeLevel level) {
    const auto& node = ir_.get(e);

    if (node.kind == Kind::ToInt && node.children.size() == 1) {
        ExprId r = purifyRec(node.children[0], level);

        if (isLinearRealExpr(r)) {
            CacheKey key{r, level};
            auto it = toIntCache_.find(key);
            if (it != toIntCache_.end()) return it->second;

            ExprId k = ir_.makeFreshVariable(ir_.intSortId(), "__nlc_floor");
            toIntCache_[key] = k;
            infos_.push_back({e, r, k, level});
            return k;
        } else {
            hasUnsupportedNonlinearToInt_ = true;
            return e;
        }
    }

    if (node.children.empty()) return e;

    SmallVector<ExprId, 4> newChildren;
    bool changed = false;
    for (ExprId c : node.children) {
        ExprId pc = purifyRec(c, level);
        newChildren.push_back(pc);
        if (pc != c) changed = true;
    }
    if (!changed) return e;

    CoreExpr ne;
    ne.kind = node.kind;
    ne.sort = node.sort;
    ne.children = std::move(newChildren);
    ne.payload = node.payload;
    return ir_.add(std::move(ne));
}

// ---------------------------------------------------------------------------
// Linear expression checks
// ---------------------------------------------------------------------------

bool LinearToIntPurifier::isLinearRealExpr(ExprId e) const {
    const auto& node = ir_.get(e);
    switch (node.kind) {
        case Kind::ConstReal:
        case Kind::ConstInt:
            return true;
        case Kind::Variable:
            return node.sort == ir_.realSortId();
        case Kind::ToReal:
            if (node.children.size() != 1) return false;
            return isLinearIntExpr(node.children[0]);
        case Kind::Add: {
            for (ExprId c : node.children)
                if (!isLinearRealExpr(c)) return false;
            return true;
        }
        case Kind::Sub:
            return node.children.size() == 2
                && isLinearRealExpr(node.children[0])
                && isLinearRealExpr(node.children[1]);
        case Kind::Neg:
            return node.children.size() == 1 && isLinearRealExpr(node.children[0]);
        case Kind::Mul:
            if (node.children.size() != 2) return false;
            return (isRationalConstant(node.children[0]) && isLinearRealExpr(node.children[1]))
                || (isRationalConstant(node.children[1]) && isLinearRealExpr(node.children[0]));
        case Kind::Div:
            if (node.children.size() != 2) return false;
            return isLinearRealExpr(node.children[0])
                && isNonZeroRationalConstant(node.children[1]);
        default:
            return false;
    }
}

bool LinearToIntPurifier::isLinearIntExpr(ExprId e) const {
    const auto& node = ir_.get(e);
    // Defensive: must be Int-sorted
    if (node.sort != ir_.intSortId()) return false;

    switch (node.kind) {
        case Kind::ConstInt:
            return true;
        case Kind::Variable:
            return node.sort == ir_.intSortId();
        case Kind::Add: {
            for (ExprId c : node.children)
                if (!isLinearIntExpr(c)) return false;
            return true;
        }
        case Kind::Sub:
            return node.children.size() == 2
                && isLinearIntExpr(node.children[0])
                && isLinearIntExpr(node.children[1]);
        case Kind::Neg:
            return node.children.size() == 1 && isLinearIntExpr(node.children[0]);
        case Kind::Mul:
            if (node.children.size() != 2) return false;
            return (isIntegerConstant(node.children[0]) && isLinearIntExpr(node.children[1]))
                || (isIntegerConstant(node.children[1]) && isLinearIntExpr(node.children[0]));
        default:
            return false;
    }
}

bool LinearToIntPurifier::isRationalConstant(ExprId e) const {
    const auto& node = ir_.get(e);
    return node.kind == Kind::ConstReal || node.kind == Kind::ConstInt;
}

bool LinearToIntPurifier::isNonZeroRationalConstant(ExprId e) const {
    const auto& node = ir_.get(e);
    if (node.kind == Kind::ConstReal) {
        if (auto* s = std::get_if<std::string>(&node.payload.value))
            return mpq_class(*s) != 0;
    }
    if (node.kind == Kind::ConstInt) {
        if (auto* v = std::get_if<int64_t>(&node.payload.value))
            return *v != 0;
    }
    return false;
}

bool LinearToIntPurifier::isIntegerConstant(ExprId e) const {
    const auto& node = ir_.get(e);
    return node.kind == Kind::ConstInt;
}

// ---------------------------------------------------------------------------
// Floor lemmas
// ---------------------------------------------------------------------------

ExprId LinearToIntPurifier::makeFloorLowerLemma(ExprId k, ExprId r) {
    ExprId toRealK = ir_.add(CoreExpr{Kind::ToReal, ir_.realSortId(), {k}, {}});
    return ir_.add(CoreExpr{Kind::Leq, ir_.boolSortId(), {toRealK, r}, {}});
}

ExprId LinearToIntPurifier::makeFloorUpperLemma(ExprId k, ExprId r) {
    ExprId toRealK = ir_.add(CoreExpr{Kind::ToReal, ir_.realSortId(), {k}, {}});
    ExprId one = ir_.add(CoreExpr{Kind::ConstReal, ir_.realSortId(), {}, Payload(std::string("1"))});
    ExprId kPlusOne = ir_.add(CoreExpr{Kind::Add, ir_.realSortId(), {toRealK, one}, {}});
    return ir_.add(CoreExpr{Kind::Lt, ir_.boolSortId(), {r, kPlusOne}, {}});
}

} // namespace nlcolver
