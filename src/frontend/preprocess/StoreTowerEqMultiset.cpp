#include "frontend/preprocess/StoreTowerEqMultiset.h"

#include <algorithm>
#include <numeric>
#include <string>
#include <gmpxx.h>

namespace xolver {

StoreTowerEqMultiset::StoreTowerEqMultiset(CoreIr& ir) : ir_(ir) {}

bool StoreTowerEqMultiset::isIntConstEq(ExprId e, int64_t v) const {
    // Robust to the parser carrying int-valued literals via ConstReal (the same
    // defensive case IntDivModConstantFold handles — see its extractIntConst).
    const CoreExpr& n = ir_.get(e);
    if (n.kind == Kind::ConstInt) {
        if (auto* p = std::get_if<int64_t>(&n.payload.value)) return *p == v;
    } else if (n.kind == Kind::ConstReal) {
        if (auto* s = std::get_if<std::string>(&n.payload.value)) {
            mpq_class q(*s);
            return q.get_den() == 1 && q.get_num() == v;
        }
    }
    return false;
}

bool StoreTowerEqMultiset::detectTower(ExprId T, ExprId& base,
                                       std::vector<ExprId>& indices) const {
    const CoreExpr& n = ir_.get(T);
    if (n.kind != Kind::Store) {        // reached the base array
        base = T;
        return true;
    }
    if (n.children.size() != 3) return false;
    ExprId prev = n.children[0];
    ExprId idx  = n.children[1];
    ExprId val  = n.children[2];

    // val must be `(+ (select prev idx) 1)` — an increment-read of the running
    // array at this index. (Add is binary here: a Select term and a ConstInt 1.)
    const CoreExpr& vn = ir_.get(val);
    if (vn.kind != Kind::Add || vn.children.size() != 2) return false;
    ExprId sel = NullExpr, one = NullExpr;
    for (ExprId c : vn.children) {
        const CoreExpr& cn = ir_.get(c);
        if (cn.kind == Kind::Select)                                 sel = c;
        else if (cn.kind == Kind::ConstInt || cn.kind == Kind::ConstReal) one = c;
    }
    if (sel == NullExpr || one == NullExpr) return false;
    if (!isIntConstEq(one, 1)) return false;
    const CoreExpr& sn = ir_.get(sel);
    if (sn.children.size() != 2) return false;
    if (sn.children[0] != prev || sn.children[1] != idx) return false;  // reads prev[idx]

    if (!detectTower(prev, base, indices)) return false;
    indices.push_back(idx);
    return true;
}

ExprId StoreTowerEqMultiset::buildMultisetEq(const std::vector<ExprId>& a,
                                             const std::vector<ExprId>& b,
                                             SortId boolSort) {
    const size_t n = a.size();
    std::vector<size_t> perm(n);
    std::iota(perm.begin(), perm.end(), 0u);
    std::vector<ExprId> disjuncts;
    do {
        std::vector<ExprId> conj;
        conj.reserve(n);
        for (size_t k = 0; k < n; ++k) {
            CoreExpr eq;
            eq.kind = Kind::Eq;
            eq.sort = boolSort;
            eq.children.push_back(a[k]);
            eq.children.push_back(b[perm[k]]);
            conj.push_back(cons(std::move(eq)));
        }
        if (conj.size() == 1) { disjuncts.push_back(conj[0]); continue; }
        CoreExpr andN;
        andN.kind = Kind::And;
        andN.sort = boolSort;
        for (ExprId c : conj) andN.children.push_back(c);
        disjuncts.push_back(cons(std::move(andN)));
    } while (std::next_permutation(perm.begin(), perm.end()));

    if (disjuncts.size() == 1) return disjuncts[0];
    CoreExpr orN;
    orN.kind = Kind::Or;
    orN.sort = boolSort;
    for (ExprId c : disjuncts) orN.children.push_back(c);
    return cons(std::move(orN));
}

ExprId StoreTowerEqMultiset::rewriteRec(ExprId e) {
    auto it = memo_.find(e);
    if (it != memo_.end()) return it->second;

    const CoreExpr& n = ir_.get(e);

    // Reduce `tower1 = tower2` over a common base to the index-multiset equality.
    if (n.kind == Kind::Eq && n.children.size() == 2) {
        ExprId b1 = NullExpr, b2 = NullExpr;
        std::vector<ExprId> i1, i2;
        if (detectTower(n.children[0], b1, i1) &&
            detectTower(n.children[1], b2, i2) &&
            !i1.empty() && i1.size() == i2.size() &&
            i1.size() <= kMaxTowerHeight && b1 == b2) {
            ExprId r = buildMultisetEq(i1, i2, n.sort);
            didRewrite_ = true;
            memo_[e] = r;
            return r;
        }
    }

    // Otherwise rebuild children bottom-up.
    CoreExpr copy = n;
    bool changed = false;
    for (auto& c : copy.children) {
        ExprId nc = rewriteRec(c);
        if (nc != c) { c = nc; changed = true; }
    }
    ExprId r = changed ? cons(std::move(copy)) : e;
    memo_[e] = r;
    return r;
}

ExprId StoreTowerEqMultiset::cons(CoreExpr e) {
    std::string key = std::to_string((int)e.kind) + ":" + std::to_string((uint32_t)e.sort);
    for (ExprId c : e.children) { key += ','; key += std::to_string((uint32_t)c); }
    if (auto* v = std::get_if<int64_t>(&e.payload.value)) { key += "#i"; key += std::to_string(*v); }
    else if (auto* s = std::get_if<std::string>(&e.payload.value)) { key += "#s"; key += *s; }
    auto it = consCache_.find(key);
    if (it != consCache_.end()) return it->second;
    ExprId id = ir_.add(std::move(e));
    consCache_[key] = id;
    return id;
}

bool StoreTowerEqMultiset::run() {
    memo_.clear();
    rewritten_.clear();
    didRewrite_ = false;
    for (const auto& [level, eid] : ir_.getScopedAssertions()) {
        rewritten_.emplace_back(level, rewriteRec(eid));
    }
    return true;
}

void StoreTowerEqMultiset::commit() {
    if (!didRewrite_) return;
    ir_.clearAssertions();
    for (const auto& [level, eid] : rewritten_) {
        ir_.addAssertion(eid, level);
    }
}

} // namespace xolver
