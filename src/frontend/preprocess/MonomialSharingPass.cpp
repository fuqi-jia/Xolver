#include "frontend/preprocess/MonomialSharingPass.h"

#include <cstdio>
#include <cstdlib>
#include <string>
#include <unordered_set>

namespace xolver {

MonomialSharingPass::MonomialSharingPass(CoreIr& ir, SortId intSort, SortId realSort, SortId boolSort)
    : ir_(ir), intSort_(intSort), realSort_(realSort), boolSort_(boolSort) {}

bool MonomialSharingPass::isShareableMul(ExprId e) const {
    const CoreExpr& n = ir_.get(e);
    if (n.kind != Kind::Mul) return false;
    if (n.children.size() < 2) return false;
    // Count non-constant children. A monomial is "nonlinear-shareable" iff
    // at least two of its factors carry runtime values — pure constants get
    // folded by the kernel and don't benefit from sharing.
    int nonConst = 0;
    for (ExprId c : n.children) {
        if (!ir_.get(c).isConst()) ++nonConst;
        if (nonConst >= 2) return true;
    }
    return false;
}

void MonomialSharingPass::collectMulRefs(ExprId root) {
    // Per-assertion visited set: a hash-consed Mul reached via multiple
    // parent paths in the SAME assertion counts as 1 reference (so the
    // sharing decision reflects "in how many DISTINCT assertions does
    // this monomial appear" — that's what gates the linearizer's
    // per-c.reason lemma multiplicity).
    std::unordered_set<ExprId> visited;
    std::vector<ExprId> stack;
    stack.push_back(root);
    while (!stack.empty()) {
        ExprId e = stack.back();
        stack.pop_back();
        if (!visited.insert(e).second) continue;
        if (isShareableMul(e)) {
            ++refCount_[e];
        }
        const CoreExpr& n = ir_.get(e);
        for (ExprId c : n.children) {
            if (!visited.count(c)) stack.push_back(c);
        }
    }
}

ExprId MonomialSharingPass::mintShareVar(SortId sort) {
    CoreExpr v;
    v.kind = Kind::Variable;
    v.sort = sort;
    v.payload = Payload(std::string("__m_share_") + std::to_string(nextAuxId_++));
    return ir_.add(std::move(v));
}

ExprId MonomialSharingPass::rewriteWithSubst(
    ExprId e, std::unordered_map<ExprId, ExprId>& memo) {

    auto it = memo.find(e);
    if (it != memo.end()) return it->second;

    auto subIt = selected_.find(e);
    if (subIt != selected_.end()) {
        memo[e] = subIt->second;
        return subIt->second;
    }

    const CoreExpr& n = ir_.get(e);
    if (n.children.empty()) {
        memo[e] = e;
        return e;
    }
    // Rewrite children first; rebuild node only if anything changed.
    std::vector<ExprId> newChildren;
    newChildren.reserve(n.children.size());
    bool changed = false;
    for (ExprId c : n.children) {
        ExprId nc = rewriteWithSubst(c, memo);
        if (nc != c) changed = true;
        newChildren.push_back(nc);
    }
    if (!changed) {
        memo[e] = e;
        return e;
    }
    CoreExpr ne;
    ne.kind = n.kind;
    ne.sort = n.sort;
    for (ExprId c : newChildren) ne.children.push_back(c);
    ne.payload = n.payload;
    ExprId out = ir_.addShared(std::move(ne));
    memo[e] = out;
    return out;
}

size_t MonomialSharingPass::run() {
    refCount_.clear();
    selected_.clear();
    defAssertions_.clear();

    const auto& scoped = ir_.getScopedAssertions();
    for (const auto& [_, a] : scoped) {
        collectMulRefs(a);
    }
    // H2 diagnostic (XOLVER_PP_MONOMIAL_SHARE_DIAG=1): print the Mul
    // refcount histogram so we can confirm the pass IS scanning when
    // selected=0 (i.e., distinguish "ran but no monomial is shared
    // structurally" from "didn't run at all" on VeryMax-class inputs).
    static const bool diag = std::getenv("XOLVER_PP_MONOMIAL_SHARE_DIAG") != nullptr;
    if (diag) {
        size_t total = refCount_.size();
        size_t shared = 0;
        int maxRef = 0;
        for (const auto& [_, c] : refCount_) {
            if (c >= 2) ++shared;
            if (c > maxRef) maxRef = c;
        }
        std::fprintf(stderr,
            "[MonomialShare-DIAG] assertions=%zu shareable-Mul-exprs=%zu "
            "with-refCount>=2: %zu  max-refCount=%d\n",
            scoped.size(), total, shared, maxRef);
    }
    // Sharing threshold: a Mul ExprId reached by >= 2 distinct assertions
    // benefits — under that bar, the linearizer would emit one cut anyway,
    // and sharing only adds the definitional constraint without saving
    // work. Tunable; 2 is the master-spec floor ("100x -> 1x" framing).
    for (const auto& [mulExpr, count] : refCount_) {
        if (count < 2) continue;
        const CoreExpr& n = ir_.get(mulExpr);
        SortId sort = (n.sort == realSort_) ? realSort_ : intSort_;
        ExprId mvar = mintShareVar(sort);

        // Build the definitional assertion (= m_var mul_expr). Note: we
        // wire the EQ to the ORIGINAL mul_expr, not its rewritten form —
        // this is the one place we MUST preserve the nonlinear atom for
        // the NIA solver to enforce. Soundness: M(mvar) = M(mul_expr)
        // under any model of the rewritten formula.
        CoreExpr eq;
        eq.kind = Kind::Eq;
        eq.sort = boolSort_;
        eq.children.push_back(mvar);
        eq.children.push_back(mulExpr);
        ExprId eqId = ir_.addShared(std::move(eq));
        defAssertions_.push_back(eqId);

        selected_[mulExpr] = mvar;
    }
    return selected_.size();
}

void MonomialSharingPass::commit() {
    if (selected_.empty()) return;
    // Rewrite every assertion through the shared substitution map.
    auto scoped = ir_.getScopedAssertions();  // copy: we'll clear + replay
    std::vector<std::pair<ScopeLevel, ExprId>> rewritten;
    rewritten.reserve(scoped.size() + defAssertions_.size());
    std::unordered_map<ExprId, ExprId> memo;
    for (const auto& [lvl, a] : scoped) {
        rewritten.push_back({lvl, rewriteWithSubst(a, memo)});
    }
    // Definitional assertions belong at scope 0 (base): they must be
    // active for the entire solve and never popped.
    for (ExprId def : defAssertions_) {
        rewritten.push_back({0, def});
    }
    ir_.clearAssertions();
    for (const auto& [lvl, a] : rewritten) {
        ir_.addAssertion(a, lvl);
    }
}

} // namespace xolver
