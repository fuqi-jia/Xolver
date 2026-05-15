#include "theory/combination/Purifier.h"
#include "theory/DebugTrace.h"
#include "expr/ir.h"
#include <iostream>

namespace nlcolver {

Purifier::Purifier(CoreIr& ir, SharedTermRegistry& registry, SortId boolSort)
    : ir_(ir), registry_(registry), boolSortId_(boolSort) {}

bool Purifier::containsUfApply(ExprId eid) const {
    const auto& e = ir_.get(eid);
    if (e.kind == Kind::UFApply) return true;
    for (ExprId child : e.children) {
        if (containsUfApply(child)) return true;
    }
    return false;
}

bool Purifier::containsArithmetic(ExprId eid) const {
    const auto& e = ir_.get(eid);
    if (e.kind == Kind::Add || e.kind == Kind::Sub || e.kind == Kind::Neg ||
        e.kind == Kind::Mul || e.kind == Kind::Div || e.kind == Kind::Mod ||
        e.kind == Kind::Abs || e.kind == Kind::Pow) {
        return true;
    }
    for (ExprId child : e.children) {
        if (containsArithmetic(child)) return true;
    }
    return false;
}

ExprId Purifier::makeFreshVar(SortId sort) {
    std::string name = "bridge_" + std::to_string(freshCounter_++);
    CoreExpr e;
    e.kind = Kind::Variable;
    e.sort = sort;
    e.payload.value = name;
    ExprId id = ir_.add(e);
    // Register in SharedTermRegistry so it appears in allSharedTerms()
    SharedTermId stid = registry_.getOrCreate(id, sort, name, true);
    registry_.addOwner(stid, TheoryId::Combination);
    NO_DBG << "[Purifier] makeFreshVar " << name << " stid=" << stid << "\n";
    return id;
}

ExprId Purifier::makeEq(ExprId lhs, ExprId rhs) {
    CoreExpr e;
    e.kind = Kind::Eq;
    e.sort = boolSortId_;
    e.children.push_back(lhs);
    e.children.push_back(rhs);
    return ir_.add(e);
}

TheoryId Purifier::theoryOf(ExprId eid) const {
    if (containsUfApply(eid)) return TheoryId::EUF;
    if (containsArithmetic(eid)) return TheoryId::LRA;
    return TheoryId::EUF;
}

void Purifier::registerEufVars(ExprId eid) {
    const auto& e = ir_.get(eid);
    if (e.kind == Kind::Variable) {
        if (auto* s = std::get_if<std::string>(&e.payload.value)) {
            SharedTermId id = registry_.getOrCreate(eid, e.sort, *s, false);
            registry_.addOwner(id, TheoryId::EUF);
            registry_.addOwner(id, TheoryId::LRA);
        }
        return;
    }
    for (ExprId child : e.children) {
        registerEufVars(child);
    }
}

ExprId Purifier::purifyRec(ExprId eid) {
    const auto& e = ir_.get(eid);

    // Leaf
    if (e.kind == Kind::Variable || e.kind == Kind::ConstBool ||
        e.kind == Kind::ConstInt || e.kind == Kind::ConstReal ||
        e.kind == Kind::ConstBV || e.kind == Kind::ConstFP) {
        return eid;
    }

    // UFApply -> bridge variable
    if (e.kind == Kind::UFApply) {
        auto it = cache_.find(eid);
        if (it != cache_.end()) {
            NO_DBG << "[Purifier] cache hit eid=" << eid << " -> eid=" << it->second << "\n";
            return it->second;
        }

        std::vector<ExprId> newArgs;
        newArgs.reserve(e.children.size());
        bool changed = false;
        for (ExprId arg : e.children) {
            ExprId p = purifyRec(arg);
            if (p != arg) changed = true;
            newArgs.push_back(p);
        }

        ExprId purifiedApply = changed
            ? ir_.add(CoreExpr{Kind::UFApply, e.sort, SmallVector<ExprId, 4>(newArgs.begin(), newArgs.end()), Payload{}})
            : eid;

        ExprId fresh = makeFreshVar(e.sort);
        ExprId bridge = makeEq(fresh, purifiedApply);
        bridgeAssertions_.push_back(bridge);
        cache_[eid] = fresh;
        NO_DBG << "[Purifier] bridge eid=" << eid << " -> eid=" << fresh
               << " bridge=" << bridge << "\n";
        return fresh;
    }

    // Arithmetic relation: replace children containing UF with bridges
    bool isArithRelation = (e.kind == Kind::Eq || e.kind == Kind::Distinct ||
                            e.kind == Kind::Lt || e.kind == Kind::Leq ||
                            e.kind == Kind::Gt || e.kind == Kind::Geq);
    if (isArithRelation && e.children.size() == 2) {
        ExprId lhs = e.children[0];
        ExprId rhs = e.children[1];
        bool lhsHasUf = containsUfApply(lhs);
        bool rhsHasUf = containsUfApply(rhs);
        if (!lhsHasUf && !rhsHasUf) return eid;

        ExprId newLhs = lhs;
        ExprId newRhs = rhs;

        if (lhsHasUf) {
            auto it = cache_.find(lhs);
            if (it != cache_.end() && it->second != lhs) {
                newLhs = it->second;
                NO_DBG << "[Purifier] arith cache hit lhs=" << lhs << " -> " << newLhs << "\n";
            } else {
                ExprId fresh = makeFreshVar(ir_.get(lhs).sort);
                cache_[lhs] = fresh;
                bridgeAssertions_.push_back(makeEq(fresh, lhs));
                newLhs = fresh;
                NO_DBG << "[Purifier] arith bridge lhs=" << lhs << " -> " << fresh << "\n";
            }
        }
        if (rhsHasUf) {
            auto it = cache_.find(rhs);
            if (it != cache_.end() && it->second != rhs) {
                newRhs = it->second;
                NO_DBG << "[Purifier] arith cache hit rhs=" << rhs << " -> " << newRhs << "\n";
            } else {
                ExprId fresh = makeFreshVar(ir_.get(rhs).sort);
                cache_[rhs] = fresh;
                bridgeAssertions_.push_back(makeEq(fresh, rhs));
                newRhs = fresh;
                NO_DBG << "[Purifier] arith bridge rhs=" << rhs << " -> " << fresh << "\n";
            }
        }
        CoreExpr ne;
        ne.kind = e.kind;
        ne.sort = boolSortId_;
        ne.children.push_back(newLhs);
        ne.children.push_back(newRhs);
        return ir_.add(ne);
    }

    // Default: recurse into children
    std::vector<ExprId> newChildren;
    newChildren.reserve(e.children.size());
    bool changed = false;
    for (ExprId child : e.children) {
        ExprId p = purifyRec(child);
        if (p != child) changed = true;
        newChildren.push_back(p);
    }
    if (!changed) return eid;

    CoreExpr ne;
    ne.kind = e.kind;
    ne.sort = e.sort;
    for (ExprId c : newChildren) ne.children.push_back(c);
    return ir_.add(ne);
}

void Purifier::purifyAssertion(ExprId eid) {
    (void)eid;
}

void Purifier::run() {
    std::vector<ExprId> original = ir_.assertions();
    std::vector<ExprId> purified;
    bridgeAssertions_.clear();
    cache_.clear();
    freshCounter_ = 0;

    for (ExprId eid : original) {
        registerEufVars(eid);
    }

    for (ExprId eid : original) {
        ExprId p = purifyRec(eid);
        purified.push_back(p);
    }

    ir_.replaceAssertions(purified);

    for (ExprId bridge : bridgeAssertions_) {
        ir_.addAssertion(bridge);
    }
}

} // namespace nlcolver
