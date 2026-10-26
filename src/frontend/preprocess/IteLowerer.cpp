#include "frontend/preprocess/IteLowerer.h"
#include "base/WorkBudget.h"
#include "ir/NumericLiteral.h"
#include <cassert>
#include <iostream>
#include <map>

namespace xolver {

namespace {
// Arithmetic atoms remain opaque: the identity holds for nonlinear terms,
// array reads and UF applications as well as for plain arithmetic variables.
struct AffineBranch {
    std::map<ExprId, mpq_class> terms;
    mpq_class constant = 0;
};

AffineBranch collectAffineBranch(const NativeTerms& ir, ExprId root, WorkBudget& budget) {
    AffineBranch result;
    std::vector<std::pair<ExprId, mpq_class>> pending{{root, 1}};
    while (!pending.empty()) {
        budget.tick();
        auto [id, factor] = std::move(pending.back());
        pending.pop_back();
        if (factor == 0) continue;
        const auto node = ir.get(id);
        if (auto value = numericLiteral(node)) {
            result.constant += factor * *value;
        } else if (node.kind == Kind::Add || node.kind == Kind::Sub || node.kind == Kind::Neg) {
            for (size_t i = 0; i < node.children.size(); ++i) {
                budget.tick();
                const bool negative = node.kind == Kind::Neg ||
                    (node.kind == Kind::Sub && (i > 0 || node.children.size() == 1));
                pending.emplace_back(node.children[i], negative ? mpq_class(-factor) : factor);
            }
        } else if (node.kind == Kind::Mul) {
            ExprId atom = NullExpr;
            bool nonlinear = false;
            mpq_class product = factor;
            for (auto child : node.children) {
                budget.tick();
                if (auto value = numericLiteral(ir, child)) product *= *value;
                else if (atom == NullExpr) atom = child;
                else { nonlinear = true; break; }
            }
            if (nonlinear) result.terms[id] += factor;
            else if (atom == NullExpr) result.constant += product;
            else pending.emplace_back(atom, std::move(product));
        } else {
            result.terms[id] += factor;
        }
    }
    for (auto it = result.terms.begin(); it != result.terms.end(); ) {
        if (it->second == 0) it = result.terms.erase(it);
        else ++it;
    }
    return result;
}

ExprId arithmeticConstant(NativeTerms& ir, SortId sort, const mpq_class& value) {
    const auto kind = ir.sortKind(sort) == SortKind::Int ? Kind::ConstInt : Kind::ConstReal;
    return ir.addShared(TermExpr{kind, sort, {}, Payload(value.get_str())});
}

ExprId buildAffineBranch(NativeTerms& ir, SortId sort, const AffineBranch& branch) {
    std::vector<ExprId> terms;
    if (branch.constant != 0) terms.push_back(arithmeticConstant(ir, sort, branch.constant));
    for (const auto& [atom, coefficient] : branch.terms) {
        if (coefficient == 1) terms.push_back(atom);
        else if (coefficient == -1)
            terms.push_back(ir.addShared(TermExpr{Kind::Neg, sort, {atom}, Payload{}}));
        else if (coefficient != 0)
            terms.push_back(ir.addShared(TermExpr{Kind::Mul, sort,
                {arithmeticConstant(ir, sort, coefficient), atom}, Payload{}}));
    }
    if (terms.empty()) return arithmeticConstant(ir, sort, 0);
    if (terms.size() == 1) return terms.front();
    TermExpr sum{Kind::Add, sort, {}, Payload{}};
    for (auto term : terms) sum.children.push_back(term);
    return ir.addShared(std::move(sum));
}

struct FactoredChoice {
    AffineBranch common, thenBranch, elseBranch;
    mpq_class scale = 1;
};

std::optional<FactoredChoice> factorArithmeticChoice(
    const NativeTerms& ir, SortId sort, ExprId thenTerm, ExprId elseTerm) {
    const auto kind = ir.sortKind(sort);
    if (kind != SortKind::Int && kind != SortKind::Real) return std::nullopt;
    auto arithmetic = [](Kind operation) {
        return operation == Kind::Add || operation == Kind::Sub ||
               operation == Kind::Neg || operation == Kind::Mul;
    };
    const auto thenNode = ir.get(thenTerm), elseNode = ir.get(elseTerm);
    if (!arithmetic(thenNode.kind) && !arithmetic(elseNode.kind)) {
        // Distinct opaque atoms have no common coefficient, and a residual
        // atom with coefficient one has no integer factor. Avoid allocating
        // affine maps for these frequent variable-selection chains.
        if (kind == SortKind::Real) return std::nullopt;
        const auto left = numericLiteral(thenNode), right = numericLiteral(elseNode);
        if (!left || !right || abs(*left - *right) <= 1) return std::nullopt;
    }
    try {
        WorkBudget budget(8192);
        FactoredChoice result;
        result.thenBranch = collectAffineBranch(ir, thenTerm, budget);
        result.elseBranch = collectAffineBranch(ir, elseTerm, budget);
        // Shift by a common constant and factor exactly shared coefficients.
        // This exposes branch-independent structure without distributing ITEs.
        result.common.constant = result.thenBranch.constant;
        result.elseBranch.constant -= result.common.constant;
        result.thenBranch.constant = 0;
        for (auto it = result.thenBranch.terms.begin(); it != result.thenBranch.terms.end(); ) {
            budget.tick();
            const auto other = result.elseBranch.terms.find(it->first);
            if (other != result.elseBranch.terms.end() && other->second == it->second) {
                result.common.terms.insert(*it);
                result.elseBranch.terms.erase(other);
                it = result.thenBranch.terms.erase(it);
            } else ++it;
        }
        if (kind == SortKind::Int) {
            mpz_class divisor = 0;
            auto include = [&](const mpq_class& coefficient) {
                budget.tick();
                if (coefficient.get_den() != 1) return false;
                mpz_gcd(divisor.get_mpz_t(), divisor.get_mpz_t(), coefficient.get_num_mpz_t());
                return true;
            };
            for (const auto* branch : {&result.thenBranch, &result.elseBranch}) {
                if (!include(branch->constant)) return std::nullopt;
                for (const auto& [atom, coefficient] : branch->terms) {
                    // Only Int-valued atoms justify divisibility. In particular
                    // an integral-looking Real expression gives no such fact.
                    if (ir.sortKind(ir.get(atom).sort) != SortKind::Int || !include(coefficient))
                        return std::nullopt;
                }
            }
            if (divisor > 1) {
                result.scale = mpq_class(divisor);
                for (auto* branch : {&result.thenBranch, &result.elseBranch}) {
                    branch->constant /= result.scale;
                    for (auto& [atom, coefficient] : branch->terms) coefficient /= result.scale;
                }
            }
        }
        if (result.common.terms.empty() && result.scale == 1) return std::nullopt;
        return result;
    } catch (const ResourceExhausted&) {
        return std::nullopt; // Optional normalization; retain exact original guards.
    }
}
} // namespace

IteLowerer::IteLowerer(NativeTerms& ir)
    : ir_(ir), boolSortId_(ir.boolSortId()) {
}

ExprId IteLowerer::freshTerm(SortId sort) {
    return ir_.makeFreshVariable(sort, "__nlc_ite", /*routingAuxiliary=*/true);
}

ExprId IteLowerer::freshBool() {
    return ir_.makeFreshVariable(boolSortId_, "__nlc_ite", /*routingAuxiliary=*/true);
}

ExprId IteLowerer::rebuildLike(ExprId original,
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

    TermExpr ne;
    ne.kind = node.kind;
    ne.sort = node.sort;
    for (ExprId c : newChildren) ne.children.push_back(c);
    ne.payload = node.payload;
    // Intern the completed native expression; registered nodes are immutable.
    return ir_.addShared(std::move(ne));
}

ExprId IteLowerer::lowerBoolIte(ExprId iteExpr) {
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

    ExprId notC = ir_.add(TermExpr{Kind::Not, boolSortId_, {cLower}, Payload{}});

    ExprId notP = ir_.add(TermExpr{Kind::Not, boolSortId_, {pLower}, Payload{}});

    ExprId notQ = ir_.add(TermExpr{Kind::Not, boolSortId_, {qLower}, Payload{}});

    ExprId notR = ir_.add(TermExpr{Kind::Not, boolSortId_, {r}, Payload{}});

    // (or (not c) (not p) r)
    ExprId clause1 = ir_.add(TermExpr{Kind::Or, boolSortId_, {notC, notP, r}, Payload{}});
    generatedAssertions_.push_back(clause1);

    // (or (not c) p (not r))
    ExprId clause2 = ir_.add(TermExpr{Kind::Or, boolSortId_, {notC, pLower, notR}, Payload{}});
    generatedAssertions_.push_back(clause2);

    // (or c (not q) r)
    ExprId clause3 = ir_.add(TermExpr{Kind::Or, boolSortId_, {cLower, notQ, r}, Payload{}});
    generatedAssertions_.push_back(clause3);

    // (or c q (not r))
    ExprId clause4 = ir_.add(TermExpr{Kind::Or, boolSortId_, {cLower, qLower, notR}, Payload{}});
    generatedAssertions_.push_back(clause4);

    return r;
}

ExprId IteLowerer::lowerTermIte(ExprId iteExpr, SortId S) {
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

    // ite(c, common + g*t, common + g*e) = common + g*ite(c,t,e).
    // For Int, the residual choice is Int too, exposing its lattice before
    // Boolean branching. The guarded residual equalities remain exact.
    auto factor = factorArithmeticChoice(ir_, S, tLower, eLower);
    if (factor) {
        tLower = buildAffineBranch(ir_, S, factor->thenBranch);
        eLower = buildAffineBranch(ir_, S, factor->elseBranch);
        if (tLower == eLower) {
            factor->common.terms[tLower] += factor->scale;
            const auto result = buildAffineBranch(ir_, S, factor->common);
            termMemo_[key] = result;
            return result;
        }
    }
    ExprId v = freshTerm(S);
    ExprId result = v;
    if (factor) {
        factor->common.terms[v] += factor->scale;
        result = buildAffineBranch(ir_, S, factor->common);
    }
    termMemo_[key] = result;

    // (or (not c) (= v t))
    ExprId eqThen = ir_.add(TermExpr{Kind::Eq, boolSortId_, {v, tLower}, Payload{}});

    ExprId notC = ir_.add(TermExpr{Kind::Not, boolSortId_, {cLower}, Payload{}});

    ExprId guardThen = ir_.add(TermExpr{Kind::Or, boolSortId_, {notC, eqThen}, Payload{}});
    generatedAssertions_.push_back(guardThen);

    // (or c (= v e))
    ExprId eqElse = ir_.add(TermExpr{Kind::Eq, boolSortId_, {v, eLower}, Payload{}});

    ExprId guardElse = ir_.add(TermExpr{Kind::Or, boolSortId_, {cLower, eqElse}, Payload{}});
    generatedAssertions_.push_back(guardElse);

    return result;
}

ExprId IteLowerer::lowerAssertion(ExprId assertion) {
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
