#include "expr/CoreIteLowerer.h"
#include <cassert>
#include <iostream>

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
    // ---------- Phase 1: classify each node as Bool-lowered or Term-lowered ----------
    // This mirrors the recursive dispatch logic of the original lowerBoolExpr/lowerExpr.
    std::unordered_set<ExprId> boolNodes;
    std::unordered_map<ExprId, SortId> termSort; // for term-lowered nodes, stores the expectedSort
    {
        std::vector<ExprId> stack;
        stack.reserve(1024);
        boolNodes.reserve(1024);
        termSort.reserve(1024);

        // Assertion is always lowered as Bool.
        stack.push_back(assertion);
        boolNodes.insert(assertion);

        while (!stack.empty()) {
            ExprId e = stack.back();
            stack.pop_back();

            const auto& node = ir_.get(e);
            bool isBoolNode = boolNodes.count(e);

            if (node.kind == Kind::Ite) {
                assert(node.children.size() == 3);
                ExprId c = node.children[0];
                ExprId t = node.children[1];
                ExprId eBranch = node.children[2];

                if (isBoolNode) {
                    // lowerBoolIte: c, p, q all go through lowerBoolExpr
                    if (boolNodes.insert(c).second) stack.push_back(c);
                    if (boolNodes.insert(t).second) stack.push_back(t);
                    if (boolNodes.insert(eBranch).second) stack.push_back(eBranch);
                } else {
                    // lowerTermIte: c goes through lowerBoolExpr, t/e go through lowerExpr(S)
                    SortId S = termSort.at(e);
                    if (boolNodes.insert(c).second) stack.push_back(c);
                    if (termSort.insert({t, S}).second) stack.push_back(t);
                    if (termSort.insert({eBranch, S}).second) stack.push_back(eBranch);
                }
            } else {
                // Non-ITE: dispatch children exactly like the recursive version
                for (ExprId child : node.children) {
                    SortId childSort = ir_.get(child).sort;
                    if (isBoolNode) {
                        // lowerBoolExpr path: childSort == boolSortId_ -> bool, else term
                        if (childSort == boolSortId_) {
                            if (boolNodes.insert(child).second) stack.push_back(child);
                        } else {
                            if (termSort.insert({child, childSort}).second) stack.push_back(child);
                        }
                    } else {
                        // lowerExpr path: expectedSort == boolSortId_ -> bool, else term
                        SortId expectedSort = termSort.at(e);
                        if (expectedSort == boolSortId_) {
                            if (boolNodes.insert(child).second) stack.push_back(child);
                        } else {
                            if (termSort.insert({child, expectedSort}).second) stack.push_back(child);
                        }
                    }
                }
            }
        }
    }

    // ---------- Phase 2: iterative post-order traversal ----------
    std::vector<ExprId> postOrder;
    {
        std::vector<ExprId> stack;
        std::unordered_set<ExprId> visited;
        stack.reserve(1024);
        visited.reserve(1024);

        // We need to traverse all nodes that were classified above.
        std::vector<ExprId> roots;
        roots.reserve(boolNodes.size() + termSort.size());
        for (ExprId e : boolNodes) roots.push_back(e);
        for (const auto& kv : termSort) roots.push_back(kv.first);

        for (ExprId root : roots) {
            if (!visited.insert(root).second) continue;
            stack.push_back(root);

            while (!stack.empty()) {
                ExprId e = stack.back();
                const auto& node = ir_.get(e);

                bool allChildrenVisited = true;
                for (ExprId child : node.children) {
                    if (boolNodes.count(child) || termSort.count(child)) {
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

    // ---------- Phase 3: process nodes in post-order ----------
    for (ExprId e : postOrder) {
        const auto& node = ir_.get(e);
        bool isBoolNode = boolNodes.count(e);

        if (node.kind == Kind::Ite) {
            if (isBoolNode) {
                lowerBoolIte(e);
            } else {
                lowerTermIte(e, termSort.at(e));
            }
        } else {
            std::vector<ExprId> newChildren;
            newChildren.reserve(node.children.size());
            for (ExprId child : node.children) {
                if (boolNodes.count(child)) {
                    newChildren.push_back(boolMemo_.at(child));
                } else {
                    newChildren.push_back(termMemo_.at({child, termSort.at(child)}));
                }
            }
            ExprId result = rebuildLike(e, newChildren);
            if (isBoolNode)
                boolMemo_[e] = result;
            else
                termMemo_[{e, termSort.at(e)}] = result;
        }
    }

    return boolMemo_.at(assertion);
}

} // namespace nlcolver
