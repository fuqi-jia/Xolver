#include "expr/CoreIteLowerer.h"
#include <cassert>
#include <iostream>

namespace xolver {

CoreIteLowerer::CoreIteLowerer(CoreIr& ir)
    : ir_(ir), boolSortId_(ir.boolSortId()) {
}

ExprId CoreIteLowerer::freshTerm(SortId sort) {
    return ir_.makeFreshVariable(sort, "__nlc_ite");
}

ExprId CoreIteLowerer::freshBool() {
    return ir_.makeFreshVariable(boolSortId_, "__nlc_ite");
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
    // iter-67: rebuildLike is the SAFE build-then-add path; the dangerous
    // empty-then-mutate Or/Not patterns at lines 66-100 still use add().
    return ir_.addShared(std::move(ne));
}

ExprId CoreIteLowerer::lowerBoolIte(ExprId iteExpr) {
    if (auto it = boolMemo_.find(iteExpr); it != boolMemo_.end())
        return it->second;

    const auto& node = ir_.get(iteExpr);
    assert(node.kind == Kind::Ite && node.children.size() == 3);

    ExprId c = node.children[0];
    ExprId p = node.children[1];
    ExprId q = node.children[2];

    // Children must already be lowered (post-order guarantees this).
    ExprId cLower = boolMemo_.at(c);
    ExprId pLower = boolMemo_.at(p);
    ExprId qLower = boolMemo_.at(q);

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

ExprId CoreIteLowerer::lowerTermIte(ExprId iteExpr, SortId S) {
    TermKey key{iteExpr, S};
    if (auto it = termMemo_.find(key); it != termMemo_.end())
        return it->second;

    const auto& node = ir_.get(iteExpr);
    assert(node.kind == Kind::Ite && node.children.size() == 3);

    ExprId c = node.children[0];
    ExprId t = node.children[1];
    ExprId e = node.children[2];

    // Children must already be lowered (post-order guarantees this).
    ExprId cLower = boolMemo_.at(c);
    ExprId tLower = termMemo_.at({t, S});
    ExprId eLower = termMemo_.at({e, S});

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

ExprId CoreIteLowerer::lowerAssertion(ExprId assertion) {
    // ---------- Phase 1: collect all work items ----------
    // Bool work items: just ExprId (lowered via lowerBoolExpr equivalent)
    // Term work items: (ExprId, SortId) pairs (lowered via lowerExpr(expectedSort) equivalent)
    std::unordered_set<ExprId> boolWork;
    std::unordered_set<TermKey, TermKeyHash> termWork;
    {
        struct WorkItem {
            ExprId e;
            std::optional<SortId> sort; // nullopt = bool, otherwise = term with this expectedSort
        };
        std::vector<WorkItem> stack;
        stack.reserve(1024);
        boolWork.reserve(1024);
        termWork.reserve(1024);

        // Assertion is always lowered as Bool.
        stack.push_back({assertion, std::nullopt});
        boolWork.insert(assertion);

        while (!stack.empty()) {
            WorkItem item = stack.back();
            stack.pop_back();

            ExprId e = item.e;
            const auto& node = ir_.get(e);
            bool isBool = !item.sort.has_value();
            SortId S = isBool ? boolSortId_ : *item.sort;

            if (node.kind == Kind::Ite) {
                assert(node.children.size() == 3);
                ExprId c = node.children[0];
                ExprId t = node.children[1];
                ExprId eBranch = node.children[2];

                if (isBool) {
                    // lowerBoolIte: c, p, q all go through lowerBoolExpr
                    if (boolWork.insert(c).second) stack.push_back({c, std::nullopt});
                    if (boolWork.insert(t).second) stack.push_back({t, std::nullopt});
                    if (boolWork.insert(eBranch).second) stack.push_back({eBranch, std::nullopt});
                } else {
                    // lowerTermIte: c goes through lowerBoolExpr, t/e go through lowerExpr(S)
                    if (boolWork.insert(c).second) stack.push_back({c, std::nullopt});
                    TermKey tKey{t, S};
                    if (termWork.insert(tKey).second) stack.push_back({t, S});
                    TermKey eKey{eBranch, S};
                    if (termWork.insert(eKey).second) stack.push_back({eBranch, S});
                }
            } else {
                // Non-ITE: dispatch children exactly like the recursive version
                for (ExprId child : node.children) {
                    SortId childSort = ir_.get(child).sort;
                    if (isBool) {
                        // lowerBoolExpr path: childSort == boolSortId_ -> bool, else term(childSort)
                        if (childSort == boolSortId_) {
                            if (boolWork.insert(child).second) stack.push_back({child, std::nullopt});
                        } else {
                            TermKey key{child, childSort};
                            if (termWork.insert(key).second) stack.push_back({child, childSort});
                        }
                    } else {
                        // lowerExpr path: S == boolSortId_ -> bool, else term(childSort)
                        if (S == boolSortId_) {
                            if (boolWork.insert(child).second) stack.push_back({child, std::nullopt});
                        } else {
                            TermKey key{child, childSort};
                            if (termWork.insert(key).second) stack.push_back({child, childSort});
                        }
                    }
                }
            }
        }
    }

    // ---------- Phase 2: post-order traversal over all reachable ExprIds ----------
    std::vector<ExprId> postOrder;
    {
        std::unordered_set<ExprId> allExprs;
        for (ExprId e : boolWork) allExprs.insert(e);
        for (const auto& key : termWork) allExprs.insert(key.expr);

        std::vector<ExprId> stack;
        std::unordered_set<ExprId> visited;
        stack.reserve(1024);
        visited.reserve(1024);

        for (ExprId root : allExprs) {
            if (!visited.insert(root).second) continue;
            stack.push_back(root);

            while (!stack.empty()) {
                ExprId e = stack.back();
                const auto& node = ir_.get(e);

                bool allChildrenVisited = true;
                for (ExprId child : node.children) {
                    if (allExprs.count(child)) {
                        if (visited.insert(child).second) {
                            stack.push_back(child);
                            allChildrenVisited = false;
                            break;
                        }
                    }
                }

                if (allChildrenVisited) {
                    postOrder.push_back(e);
                    stack.pop_back();
                }
            }
        }
    }

    // ---------- Phase 3: process all work items for each ExprId in post-order ----------
    // Build a map from ExprId -> its term-work expected sorts for O(1) lookup.
    std::unordered_map<ExprId, std::vector<SortId>> termWorkByExpr;
    termWorkByExpr.reserve(termWork.size());
    for (const auto& key : termWork) {
        termWorkByExpr[key.expr].push_back(key.expectedSort);
    }

    for (ExprId e : postOrder) {
        // Copy the node because lowerBoolIte / lowerTermIte / rebuildLike
        // may call ir_.add(), which can reallocate the internal expr vector
        // and invalidate references.
        const auto node = ir_.get(e);

        // Process bool work item first (if any)
        if (boolWork.count(e)) {
            if (node.kind == Kind::Ite) {
                lowerBoolIte(e);
            } else {
                std::vector<ExprId> newChildren;
                newChildren.reserve(node.children.size());
                for (ExprId child : node.children) {
                    if (boolWork.count(child)) {
                        newChildren.push_back(boolMemo_.at(child));
                    } else {
                        SortId childSort = ir_.get(child).sort;
                        newChildren.push_back(termMemo_.at({child, childSort}));
                    }
                }
                ExprId result = rebuildLike(e, newChildren);
                boolMemo_[e] = result;
            }
        }

        // Process all term work items for this ExprId
        auto it = termWorkByExpr.find(e);
        if (it != termWorkByExpr.end()) {
            for (SortId S : it->second) {
                if (node.kind == Kind::Ite) {
                    lowerTermIte(e, S);
                } else {
                    std::vector<ExprId> newChildren;
                    newChildren.reserve(node.children.size());
                    for (ExprId child : node.children) {
                        if (boolWork.count(child)) {
                            newChildren.push_back(boolMemo_.at(child));
                        } else {
                            SortId childSort = ir_.get(child).sort;
                            newChildren.push_back(termMemo_.at({child, childSort}));
                        }
                    }
                    ExprId result = rebuildLike(e, newChildren);
                    termMemo_[{e, S}] = result;
                }
            }
        }
    }

    return boolMemo_.at(assertion);
}

} // namespace xolver
