#include "frontend/preprocess/ArrayReadOverWrite.h"
#include "util/EnvParam.h"

#include <cstdio>
#include <cstdlib>
#include <unordered_set>

namespace xolver {

namespace {
struct RowDiag { size_t selConst = 0, foldVal = 0, peelResidual = 0,
                 blockedVar = 0, defFollow = 0, arrDefs = 0; };
RowDiag g_rowDiag;
bool rowDiagOn() {
    static const bool on = [] {
        return xolver::env::flag("XOLVER_PP_ROW_FOLD_DIAG");
    }();
    return on;
}
} // namespace

ArrayReadOverWrite::ArrayReadOverWrite(CoreIr& ir) : ir_(ir) {}

bool ArrayReadOverWrite::isArraySort(SortId s) const {
    auto k = ir_.sortKind(s);
    return k && *k == SortKind::Array;
}

void ArrayReadOverWrite::buildArrayDefs() {
    arrDef_.clear();
    // Walk top-level conjuncts only (And is the unconditional connective).
    std::vector<ExprId> work;
    for (const auto& [level, eid] : ir_.getScopedAssertions()) work.push_back(eid);
    std::unordered_set<ExprId> seen;
    while (!work.empty()) {
        ExprId e = work.back(); work.pop_back();
        if (!seen.insert(e).second) continue;
        const CoreExpr& n = ir_.get(e);
        if (n.kind == Kind::And) {
            for (ExprId c : n.children) work.push_back(c);
            continue;
        }
        if (n.kind == Kind::Eq && n.children.size() == 2) {
            ExprId L = n.children[0], R = n.children[1];
            const CoreExpr& ln = ir_.get(L);
            const CoreExpr& rn = ir_.get(R);
            // Map an array-sorted Variable to the other (array-sorted) side.
            if (ln.kind == Kind::Variable && isArraySort(ln.sort) && isArraySort(rn.sort)
                && R != L && !arrDef_.count(L)) {
                arrDef_[L] = R;
            } else if (rn.kind == Kind::Variable && isArraySort(rn.sort) && isArraySort(ln.sort)
                       && R != L && !arrDef_.count(R)) {
                arrDef_[R] = L;
            }
        }
    }
    if (rowDiagOn()) g_rowDiag.arrDefs = arrDef_.size();
}

bool ArrayReadOverWrite::intConstVal(ExprId e, mpz_class& out) const {
    // Robust to the parser carrying int-valued literals via ConstReal (the same
    // defensive case StoreTowerEqMultiset / IntDivModConstantFold handle).
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

ExprId ArrayReadOverWrite::resolveSelect(ExprId arr, ExprId idx, SortId sort,
                                         ExprId orig) {
    mpz_class ci;
    if (intConstVal(idx, ci)) {
        if (rowDiagOn()) ++g_rowDiag.selConst;
        // Walk the store chain from the outermost store inward, threading through
        // top-level array def-var equations. `visited` guards against a cyclic
        // definition (e.g. `(= a (store a 0 ...))`).
        ExprId cur = arr;
        std::unordered_set<ExprId> visited;
        while (true) {
            const CoreExpr& n = ir_.get(cur);
            if (n.kind == Kind::Store && n.children.size() == 3) {
                mpz_class si;
                if (intConstVal(n.children[1], si)) {
                    if (si == ci) {                 // i == j: read returns v
                        didRewrite_ = true;
                        if (rowDiagOn()) ++g_rowDiag.foldVal;
                        return n.children[2];
                    }
                    cur = n.children[0];            // i != j: skip this store
                    continue;
                }
                if (rowDiagOn() && cur != arr) ++g_rowDiag.blockedVar;
                break;                              // variable store index: stop
            }
            if (n.kind == Kind::ConstArray && n.children.size() == 1) {
                didRewrite_ = true;                 // select(const-array(v), _) = v
                if (rowDiagOn()) ++g_rowDiag.foldVal;
                return n.children[0];
            }
            if (n.kind == Kind::Variable && visited.insert(cur).second) {
                auto it = arrDef_.find(cur);
                if (it != arrDef_.end()) {          // follow `arrvar = T` (sound)
                    cur = rewriteRec(it->second);
                    if (rowDiagOn()) ++g_rowDiag.defFollow;
                    continue;
                }
            }
            break;                                  // base var / select / etc.
        }
        if (cur != arr) {                           // peeled >=1 store: residual
            didRewrite_ = true;
            if (rowDiagOn()) ++g_rowDiag.peelResidual;
            return ir_.add(CoreExpr{Kind::Select, sort, {cur, idx}, {}});
        }
    }
    // No read-over-write reduction. Rebuild the select only if a child changed.
    const CoreExpr& on = ir_.get(orig);
    if (on.children.size() == 2 && arr == on.children[0] && idx == on.children[1])
        return orig;
    return ir_.add(CoreExpr{Kind::Select, sort, {arr, idx}, {}});
}

ExprId ArrayReadOverWrite::rewriteRec(ExprId e) {
    auto it = memo_.find(e);
    if (it != memo_.end()) return it->second;
    // Re-entrant on `e` (cyclic array definition reached via def-following):
    // leave it unchanged rather than recurse forever. Sound — we simply do not
    // simplify the cyclic node. Do not memoize (the outer call finalizes it).
    if (!inProgress_.insert(e).second) return e;

    const CoreExpr& n = ir_.get(e);
    ExprId r;
    if (n.kind == Kind::Select && n.children.size() == 2) {
        ExprId arr = rewriteRec(n.children[0]);
        ExprId idx = rewriteRec(n.children[1]);
        r = resolveSelect(arr, idx, n.sort, e);
    } else {
        CoreExpr copy = n;
        bool changed = false;
        for (auto& c : copy.children) {
            ExprId nc = rewriteRec(c);
            if (nc != c) { c = nc; changed = true; }
        }
        r = changed ? ir_.add(std::move(copy)) : e;
    }
    inProgress_.erase(e);
    memo_[e] = r;
    return r;
}

bool ArrayReadOverWrite::run() {
    memo_.clear();
    rewritten_.clear();
    didRewrite_ = false;
    buildArrayDefs();
    for (const auto& [level, eid] : ir_.getScopedAssertions()) {
        rewritten_.emplace_back(level, rewriteRec(eid));
    }
    if (rowDiagOn()) {
        std::fprintf(stderr,
            "[ROW-FOLD] arrDefs=%zu selConst=%zu foldVal=%zu peelResidual=%zu "
            "blockedVar=%zu defFollow=%zu exprTableNow=%zu\n",
            g_rowDiag.arrDefs, g_rowDiag.selConst, g_rowDiag.foldVal,
            g_rowDiag.peelResidual, g_rowDiag.blockedVar, g_rowDiag.defFollow,
            ir_.size());
        std::fflush(stderr);
    }
    return didRewrite_;
}

void ArrayReadOverWrite::commit() {
    if (!didRewrite_) return;
    ir_.clearAssertions();
    for (const auto& [level, eid] : rewritten_) {
        ir_.addAssertion(eid, level);
    }
}

} // namespace xolver
