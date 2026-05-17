#include "expr/CoreIteLowerer.h"
#include <cassert>

namespace nlcolver {

CoreIteLowerer::CoreIteLowerer(CoreIr& ir)
    : ir_(ir), boolSortId_(ir.boolSortId()) {
    // Scan existing variable names to avoid collision with fresh symbols.
    for (ExprId id = 0; id < static_cast<ExprId>(ir_.size()); ++id) {
        const auto& e = ir_.get(id);
        if (e.kind == Kind::Variable) {
            if (auto* s = std::get_if<std::string>(&e.payload.value)) {
                usedNames_.insert(*s);
            }
        }
    }
}

std::string CoreIteLowerer::makeUniqueName(const std::string& prefix) {
    std::string name;
    do {
        name = prefix + "_" + std::to_string(freshCounter_++);
    } while (usedNames_.count(name));
    usedNames_.insert(name);
    return name;
}

ExprId CoreIteLowerer::freshTerm(SortId sort) {
    std::string name = makeUniqueName("__nlc_ite");
    CoreExpr e;
    e.kind = Kind::Variable;
    e.sort = sort;
    e.payload = Payload(std::move(name));
    return ir_.add(std::move(e));
}

ExprId CoreIteLowerer::freshBool() {
    std::string name = makeUniqueName("__nlc_ite");
    CoreExpr e;
    e.kind = Kind::Variable;
    e.sort = boolSortId_;
    e.payload = Payload(std::move(name));
    return ir_.add(std::move(e));
}

ExprId CoreIteLowerer::rebuildLike(ExprId original,
                                   const std::vector<ExprId>& newChildren) {
    const auto& node = ir_.get(original);

    bool changed = false;
    for (size_t i = 0; i < newChildren.size(); ++i) {
        if (newChildren[i] != node.children[i]) {
            changed = true;
            break;
        }
    }

    if (!changed) return original;

    CoreExpr ne;
    ne.kind = node.kind;
    ne.sort = node.sort;
    for (ExprId c : newChildren) ne.children.push_back(c);
    ne.payload = node.payload;
    return ir_.add(std::move(ne));
}

ExprId CoreIteLowerer::lowerBoolExpr(ExprId e) {
    if (auto it = boolMemo_.find(e); it != boolMemo_.end())
        return it->second;

    const auto& node = ir_.get(e);

    if (node.kind == Kind::Ite) {
        ExprId result = lowerBoolIte(e);
        boolMemo_[e] = result;
        return result;
    }

    std::vector<ExprId> newChildren;
    newChildren.reserve(node.children.size());
    for (ExprId child : node.children) {
        SortId childSort = ir_.get(child).sort;
        if (childSort == boolSortId_)
            newChildren.push_back(lowerBoolExpr(child));
        else
            newChildren.push_back(lowerExpr(child, childSort));
    }

    ExprId result = rebuildLike(e, newChildren);
    boolMemo_[e] = result;
    return result;
}

ExprId CoreIteLowerer::lowerExpr(ExprId e, SortId expectedSort) {
    // Bool expressions always go through lowerBoolExpr to avoid dual-memo issue.
    if (expectedSort == boolSortId_)
        return lowerBoolExpr(e);

    TermKey key{e, expectedSort};
    if (auto it = termMemo_.find(key); it != termMemo_.end())
        return it->second;

    const auto& node = ir_.get(e);

    if (node.kind == Kind::Ite) {
        ExprId result = lowerTermIte(e, expectedSort);
        termMemo_[key] = result;
        return result;
    }

    std::vector<ExprId> newChildren;
    newChildren.reserve(node.children.size());
    for (ExprId child : node.children) {
        SortId childSort = ir_.get(child).sort;
        if (childSort == boolSortId_)
            newChildren.push_back(lowerBoolExpr(child));
        else
            newChildren.push_back(lowerExpr(child, childSort));
    }

    ExprId result = rebuildLike(e, newChildren);
    termMemo_[key] = result;
    return result;
}

ExprId CoreIteLowerer::lowerTermIte(ExprId iteExpr, SortId S) {
    TermKey key{iteExpr, S};
    if (auto it = termMemo_.find(key); it != termMemo_.end())
        return it->second;

    const auto& node = ir_.get(iteExpr);
    assert(node.kind == Kind::Ite && node.children.size() == 3);

    ExprId c = node.children[0];
    ExprId t = node.children[1];
    ExprId e = node.children[2];

    ExprId cLower = lowerBoolExpr(c);
    ExprId tLower = lowerExpr(t, S);
    ExprId eLower = lowerExpr(e, S);

    // Optimization: ite(c, t, t) -> t
    if (tLower == eLower) {
        termMemo_[key] = tLower;
        return tLower;
    }

    ExprId v = freshTerm(S);
    termMemo_[key] = v;

    // (or (not c) (= v t))
    ExprId eqThen = ir_.add(CoreExpr{Kind::Eq, boolSortId_, {}, Payload{}});
    ir_.get(eqThen).children.push_back(v);
    ir_.get(eqThen).children.push_back(tLower);

    ExprId notC = ir_.add(CoreExpr{Kind::Not, boolSortId_, {}, Payload{}});
    ir_.get(notC).children.push_back(cLower);

    ExprId guardThen = ir_.add(CoreExpr{Kind::Or, boolSortId_, {}, Payload{}});
    ir_.get(guardThen).children.push_back(notC);
    ir_.get(guardThen).children.push_back(eqThen);
    generatedAssertions_.push_back(guardThen);

    // (or c (= v e))
    ExprId eqElse = ir_.add(CoreExpr{Kind::Eq, boolSortId_, {}, Payload{}});
    ir_.get(eqElse).children.push_back(v);
    ir_.get(eqElse).children.push_back(eLower);

    ExprId guardElse = ir_.add(CoreExpr{Kind::Or, boolSortId_, {}, Payload{}});
    ir_.get(guardElse).children.push_back(cLower);
    ir_.get(guardElse).children.push_back(eqElse);
    generatedAssertions_.push_back(guardElse);

    return v;
}

ExprId CoreIteLowerer::lowerBoolIte(ExprId iteExpr) {
    if (auto it = boolMemo_.find(iteExpr); it != boolMemo_.end())
        return it->second;

    const auto& node = ir_.get(iteExpr);
    assert(node.kind == Kind::Ite && node.children.size() == 3);

    ExprId c = node.children[0];
    ExprId p = node.children[1];
    ExprId q = node.children[2];

    ExprId cLower = lowerBoolExpr(c);
    ExprId pLower = lowerBoolExpr(p);
    ExprId qLower = lowerBoolExpr(q);

    // Optimization: ite(c, p, p) -> p
    if (pLower == qLower) {
        boolMemo_[iteExpr] = pLower;
        return pLower;
    }

    ExprId r = freshBool();
    boolMemo_[iteExpr] = r;

    ExprId notC = ir_.add(CoreExpr{Kind::Not, boolSortId_, {}, Payload{}});
    ir_.get(notC).children.push_back(cLower);

    ExprId notP = ir_.add(CoreExpr{Kind::Not, boolSortId_, {}, Payload{}});
    ir_.get(notP).children.push_back(pLower);

    ExprId notQ = ir_.add(CoreExpr{Kind::Not, boolSortId_, {}, Payload{}});
    ir_.get(notQ).children.push_back(qLower);

    ExprId notR = ir_.add(CoreExpr{Kind::Not, boolSortId_, {}, Payload{}});
    ir_.get(notR).children.push_back(r);

    // (or (not c) (not p) r)
    ExprId clause1 = ir_.add(CoreExpr{Kind::Or, boolSortId_, {}, Payload{}});
    ir_.get(clause1).children.push_back(notC);
    ir_.get(clause1).children.push_back(notP);
    ir_.get(clause1).children.push_back(r);
    generatedAssertions_.push_back(clause1);

    // (or (not c) p (not r))
    ExprId clause2 = ir_.add(CoreExpr{Kind::Or, boolSortId_, {}, Payload{}});
    ir_.get(clause2).children.push_back(notC);
    ir_.get(clause2).children.push_back(pLower);
    ir_.get(clause2).children.push_back(notR);
    generatedAssertions_.push_back(clause2);

    // (or c (not q) r)
    ExprId clause3 = ir_.add(CoreExpr{Kind::Or, boolSortId_, {}, Payload{}});
    ir_.get(clause3).children.push_back(cLower);
    ir_.get(clause3).children.push_back(notQ);
    ir_.get(clause3).children.push_back(r);
    generatedAssertions_.push_back(clause3);

    // (or c q (not r))
    ExprId clause4 = ir_.add(CoreExpr{Kind::Or, boolSortId_, {}, Payload{}});
    ir_.get(clause4).children.push_back(cLower);
    ir_.get(clause4).children.push_back(qLower);
    ir_.get(clause4).children.push_back(notR);
    generatedAssertions_.push_back(clause4);

    return r;
}

ExprId CoreIteLowerer::lowerAssertion(ExprId assertion) {
    return lowerBoolExpr(assertion);
}

} // namespace nlcolver
