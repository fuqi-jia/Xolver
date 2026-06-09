#include "frontend/preprocess/targeted/UfApplyAckermann.h"

#include <cstdio>
#include <cstdlib>

namespace xolver {

UfApplyAckermann::UfApplyAckermann(CoreIr& ir) : ir_(ir) {}

bool UfApplyAckermann::isScalarSort(SortId s) const {
    return s == ir_.intSortId() || s == ir_.realSortId();
}

bool UfApplyAckermann::intConstVal(ExprId e, mpz_class& out) const {
    const CoreExpr& n = ir_.get(e);
    if (n.kind == Kind::ConstInt) {
        if (auto* p = std::get_if<int64_t>(&n.payload.value)) { out = *p; return true; }
    } else if (n.kind == Kind::ConstReal) {
        if (auto* s = std::get_if<std::string>(&n.payload.value)) {
            mpq_class q(*s);
            if (q.get_den() == 1) { out = q.get_num(); return true; }
        }
    }
    return false;
}

ExprId UfApplyAckermann::rewriteRec(ExprId e) {
    auto it = memo_.find(e);
    if (it != memo_.end()) return it->second;
    if (!inProgress_.insert(e).second) return e;

    const CoreExpr& n = ir_.get(e);
    ExprId r;
    if (n.kind == Kind::UFApply && isScalarSort(n.sort)) {
        // Rewrite args first, then Ackermannize this application.
        std::vector<ExprId> args;
        args.reserve(n.children.size());
        for (ExprId c : n.children) args.push_back(rewriteRec(c));
        std::string fn;
        if (auto* s = std::get_if<std::string>(&n.payload.value)) fn = *s;
        AppKey key{fn, args};
        auto ait = appVar_.find(key);
        if (ait == appVar_.end()) {
            ExprId fv = ir_.makeFreshVariable(n.sort, "ufack");
            appVar_.emplace(key, fv);
            byFn_[fn].emplace_back(args, fv);
            r = fv;
        } else {
            r = ait->second;
        }
        didRewrite_ = true;
    } else {
        CoreExpr copy = n;
        bool changed = false;
        for (auto& c : copy.children) {
            ExprId nc = rewriteRec(c);
            if (nc != c) { c = nc; changed = true; }
        }
        r = changed ? ir_.addShared(std::move(copy)) : e;
    }
    inProgress_.erase(e);
    memo_[e] = r;
    return r;
}

void UfApplyAckermann::buildCongruences() {
    const SortId boolS = ir_.boolSortId();
    for (auto& [fn, apps] : byFn_) {
        (void)fn;
        for (size_t i = 0; i < apps.size(); ++i) {
            for (size_t j = i + 1; j < apps.size(); ++j) {
                const auto& ai = apps[i].first;
                const auto& aj = apps[j].first;
                if (ai.size() != aj.size()) continue;     // arity mismatch (overload): independent
                bool provablyDistinct = false;
                std::vector<ExprId> eqs;
                for (size_t k = 0; k < ai.size(); ++k) {
                    ExprId a = ai[k], b = aj[k];
                    if (a == b) continue;
                    mpz_class ca, cb;
                    if (intConstVal(a, ca) && intConstVal(b, cb)) {
                        if (ca != cb) { provablyDistinct = true; break; }
                        continue;
                    }
                    eqs.push_back(ir_.addShared(CoreExpr{Kind::Eq, boolS, {a, b}, {}}));
                }
                if (provablyDistinct) continue;
                ExprId cons = ir_.addShared(CoreExpr{Kind::Eq, boolS,
                              {apps[i].second, apps[j].second}, {}});
                if (eqs.empty()) {
                    // All argument pairs are equal (syntactically, or value-equal
                    // constants with distinct ExprIds): the applications are
                    // CONGRUENT, so their values must be equal UNCONDITIONALLY.
                    // (Skipping here was unsound — it left two fresh vars for the
                    // same f(c) unlinked, e.g. f(1+1) vs f(2).)
                    extra_.push_back(cons);
                    continue;
                }
                ExprId ante = eqs.size() == 1
                    ? eqs[0]
                    : ir_.addShared(CoreExpr{Kind::And, boolS,
                              SmallVector<ExprId, 4>(eqs.begin(), eqs.end()), {}});
                extra_.push_back(ir_.addShared(CoreExpr{Kind::Implies, boolS, {ante, cons}, {}}));
            }
        }
    }
}

bool UfApplyAckermann::run() {
    memo_.clear();
    inProgress_.clear();
    rewritten_.clear();
    extra_.clear();
    appVar_.clear();
    byFn_.clear();
    didRewrite_ = false;

    // Cheap guard: only proceed if a scalar UF application exists.
    bool any = false;
    {
        std::unordered_set<ExprId> seen;
        std::vector<ExprId> work;
        for (const auto& [level, eid] : ir_.getScopedAssertions()) { (void)level; work.push_back(eid); }
        while (!work.empty() && !any) {
            ExprId e = work.back(); work.pop_back();
            if (!seen.insert(e).second) continue;
            const CoreExpr& n = ir_.get(e);
            if (n.kind == Kind::UFApply && isScalarSort(n.sort)) { any = true; break; }
            for (ExprId c : n.children) work.push_back(c);
        }
    }
    if (!any) return false;

    for (const auto& [level, eid] : ir_.getScopedAssertions())
        rewritten_.emplace_back(level, rewriteRec(eid));
    if (!didRewrite_) return false;
    buildCongruences();

    if (std::getenv("XOLVER_TARGETED_PP_DIAG"))
        std::fprintf(stderr, "[UFACK] apps=%zu congruences=%zu\n",
                     appVar_.size(), extra_.size());
    return true;
}

void UfApplyAckermann::commit() {
    if (!didRewrite_) return;
    int baseLevel = 0;
    if (!rewritten_.empty()) {
        baseLevel = rewritten_.front().first;
        for (const auto& [lvl, eid] : rewritten_) { (void)eid; if (lvl < baseLevel) baseLevel = lvl; }
    }
    ir_.clearAssertions();
    for (const auto& [level, eid] : rewritten_) ir_.addAssertion(eid, level);
    for (ExprId c : extra_) ir_.addAssertion(c, baseLevel);
}

} // namespace xolver
