#include "frontend/preprocess/targeted/ReadOnlyArrayElim.h"
#include "expr/Smt2Dumper.h"

#include <algorithm>
#include <cstdio>
#include <cstdlib>

namespace xolver {

ReadOnlyArrayElim::ReadOnlyArrayElim(CoreIr& ir) : ir_(ir) {}

bool ReadOnlyArrayElim::isArraySort(SortId s) const {
    auto k = ir_.sortKind(s);
    return k && *k == SortKind::Array;
}

bool ReadOnlyArrayElim::intConstVal(ExprId e, mpz_class& out) const {
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

void ReadOnlyArrayElim::scanNode(ExprId e, std::unordered_set<ExprId>& seen) {
    if (bailed_) return;
    if (!seen.insert(e).second) return;
    // A `(= S W)` to be replaced by `false` is opaque to the read-only scan:
    // its subtree (the store-expression S etc.) is discarded, so it need not
    // satisfy the read-only fragment rules. Reads of W referenced elsewhere are
    // scanned via their other occurrences.
    if (falseEqNodes_.count(e)) return;
    const CoreExpr& n = ir_.get(e);

    // (a) Any store / const-array means the array is written: not read-only.
    if (n.kind == Kind::Store || n.kind == Kind::ConstArray) { bailed_ = true; return; }

    // (b) An array-sorted term may only be a base Variable or a Select chain.
    //     Anything else array-sorted (array-valued ITE, UF returning an array,
    //     etc.) is outside the fragment we can soundly Ackermannize.
    if (isArraySort(n.sort) && n.kind != Kind::Variable && n.kind != Kind::Select) {
        bailed_ = true; return;
    }

    // (c) An array-sorted term may only occur as the array operand (child 0) of
    //     a Select. Catches array equality/disequality, arrays passed to UF, an
    //     array stuffed into an ITE branch, etc.
    for (size_t ci = 0; ci < n.children.size(); ++ci) {
        ExprId c = n.children[ci];
        if (isArraySort(ir_.get(c).sort) && !(n.kind == Kind::Select && ci == 0)) {
            bailed_ = true; return;
        }
    }
    for (ExprId c : n.children) {
        scanNode(c, seen);
        if (bailed_) return;
    }
}

bool ReadOnlyArrayElim::collectFalseEqs() {
    // Gather all Store array-operands (a Variable used as child 0 of a Store is a
    // "written" array — NOT free) and all array-sorted equalities.
    std::unordered_set<ExprId> storeOperands;
    std::vector<ExprId> arrayEqs;
    std::unordered_set<ExprId> seen;
    std::vector<ExprId> work;
    for (const auto& [level, eid] : ir_.getScopedAssertions()) { (void)level; work.push_back(eid); }
    while (!work.empty()) {
        ExprId e = work.back(); work.pop_back();
        if (!seen.insert(e).second) continue;
        const CoreExpr& n = ir_.get(e);
        if (n.kind == Kind::Store && !n.children.empty()) storeOperands.insert(n.children[0]);
        if (n.children.size() == 2 && isArraySort(ir_.get(n.children[0]).sort)) {
            if (n.kind == Kind::Eq) arrayEqs.push_back(e);
            else if (n.kind == Kind::Distinct) return false;  // array Distinct: not handled yet
        }
        for (ExprId c : n.children) work.push_back(c);
    }
    if (arrayEqs.empty()) return true;   // store-free R1 path: nothing to do here
    // An array equality is falsifiable iff at least one side is an array Variable
    // that is never a Store operand (a free array): W can always be chosen != S
    // at an unread index, so the equality is false. Mark W free + the Eq for
    // `false` replacement. Bail on any array equality with no free-variable side.
    for (ExprId eqNode : arrayEqs) {
        const CoreExpr& n = ir_.get(eqNode);
        ExprId a = n.children[0], b = n.children[1];
        ExprId w = NullExpr;
        if (ir_.get(a).kind == Kind::Variable && !storeOperands.count(a)) w = a;
        else if (ir_.get(b).kind == Kind::Variable && !storeOperands.count(b)) w = b;
        if (w == NullExpr) return false;            // non-falsifiable array eq -> bail
        freeArrayVars_.insert(w);
        falseEqNodes_.insert(eqNode);
    }
    return true;
}

bool ReadOnlyArrayElim::safeToEliminate() {
    // There must be at least one array sort in play, else nothing to do.
    bool anyArray = false;
    std::unordered_set<ExprId> seen;
    for (const auto& [level, eid] : ir_.getScopedAssertions()) {
        (void)level;
        scanNode(eid, seen);
        if (bailed_) return false;
    }
    for (ExprId id : seen) {
        if (isArraySort(ir_.get(id).sort)) { anyArray = true; break; }
    }
    return anyArray;
}

bool ReadOnlyArrayElim::analyzeRead(ExprId arr, ExprId idx, ReadKey& key) {
    key.base = NullExpr;
    key.path.clear();
    key.path.push_back(idx);
    ExprId cur = arr;
    for (int depth = 0; depth < 16; ++depth) {
        const CoreExpr& n = ir_.get(cur);
        if (n.kind == Kind::Variable && isArraySort(n.sort)) {
            key.base = cur;
            return true;
        }
        if (n.kind == Kind::Select && isArraySort(n.sort) && n.children.size() == 2) {
            key.path.push_back(n.children[1]);   // already-rewritten inner index
            cur = n.children[0];
            continue;
        }
        return false;
    }
    return false;
}

ExprId ReadOnlyArrayElim::rewriteRec(ExprId e) {
    if (bailed_) return e;
    auto it = memo_.find(e);
    if (it != memo_.end()) return it->second;
    if (!inProgress_.insert(e).second) return e;     // defensive cycle guard

    // Write-array mode: `(= S W)` with W a free read-only array var -> `false`
    // (W can always differ from S). Drops the whole store-expression S.
    if (falseEqNodes_.count(e)) {
        ExprId f = ir_.addShared(CoreExpr{Kind::ConstBool, ir_.boolSortId(), {}, Payload(false)});
        inProgress_.erase(e);
        memo_[e] = f;
        didRewrite_ = true;
        usedWriteArray_ = true;
        return f;
    }

    const CoreExpr& n = ir_.get(e);
    ExprId r;
    if (n.kind == Kind::Select && n.children.size() == 2 && !isArraySort(n.sort)) {
        // Scalar leaf read: rewrite operands, then Ackermannize.
        ExprId arr = rewriteRec(n.children[0]);
        ExprId idx = rewriteRec(n.children[1]);
        ReadKey key;
        if (analyzeRead(arr, idx, key)) {
            auto rit = readVar_.find(key);
            if (rit == readVar_.end()) {
                ExprId fv = ir_.makeFreshVariable(n.sort, "roae");
                readVar_.emplace(key, fv);
                readList_.emplace_back(key, fv);
                std::string nm;
                if (auto* s = std::get_if<std::string>(&ir_.get(fv).payload.value)) nm = *s;
                // arr/idx are the (rewritten) operands of the outermost scalar
                // select — exactly the (array-operand, index) the validator keys
                // its select override on, and hash-cons-stable in the original
                // snapshot the validator walks.
                reads_.push_back(ReadRec{arr, idx, fv, std::move(nm)});
                r = fv;
            } else {
                r = rit->second;
            }
            didRewrite_ = true;
        } else {
            // Should not happen after safeToEliminate(); rebuild conservatively.
            const CoreExpr& on = ir_.get(e);
            if (arr == on.children[0] && idx == on.children[1]) r = e;
            else r = ir_.addShared(CoreExpr{Kind::Select, n.sort, {arr, idx}, {}});
        }
    } else {
        CoreExpr copy = n;
        bool changed = false;
        for (auto& c : copy.children) {
            ExprId nc = rewriteRec(c);
            if (nc != c) { c = nc; changed = true; }
        }
        // Canonicalize commutative-associative arithmetic operands: FLATTEN
        // nested same-kind children, then SORT by ExprId. Replacing reads with
        // fresh vars leaves two value-equal sums that differ in operand order
        // AND in associative nesting across assertions (the SV-COMP cases write
        // the same memory sum shuffled and re-parenthesised). A flat+sorted
        // canonical form merges them via the IR hash-cons into ONE `(+ ...)`
        // node, so the downstream div/mod lowering emits ONE quotient/remainder
        // system instead of several it must then prove mutually consistent —
        // which is exactly what wedged the solve. Sound: + and * are commutative
        // and associative.
        if (changed && (copy.kind == Kind::Add || copy.kind == Kind::Mul)) {
            SmallVector<ExprId, 4> flat;
            for (ExprId c : copy.children) {
                const CoreExpr& cn = ir_.get(c);
                if (cn.kind == copy.kind)
                    for (ExprId gc : cn.children) flat.push_back(gc);
                else
                    flat.push_back(c);
            }
            std::sort(flat.begin(), flat.end());
            copy.children = std::move(flat);
        }
        r = changed ? ir_.addShared(std::move(copy)) : e;
    }
    inProgress_.erase(e);
    memo_[e] = r;
    return r;
}

void ReadOnlyArrayElim::buildCongruences() {
    const SortId boolS = ir_.boolSortId();
    for (size_t i = 0; i < readList_.size(); ++i) {
        for (size_t j = i + 1; j < readList_.size(); ++j) {
            const ReadKey& ki = readList_[i].first;
            const ReadKey& kj = readList_[j].first;
            if (ki.base != kj.base) continue;                 // distinct free arrays: independent
            if (ki.path.size() != kj.path.size()) continue;   // sort-incompatible: independent

            bool provablyDistinct = false;
            std::vector<ExprId> eqs;
            for (size_t k = 0; k < ki.path.size(); ++k) {
                ExprId a = ki.path[k], b = kj.path[k];
                if (a == b) continue;                          // syntactically equal index
                mpz_class ca, cb;
                if (intConstVal(a, ca) && intConstVal(b, cb)) {
                    if (ca != cb) { provablyDistinct = true; break; }
                    continue;                                  // equal constants
                }
                eqs.push_back(ir_.addShared(CoreExpr{Kind::Eq, boolS, {a, b}, {}}));
            }
            if (provablyDistinct) continue;                    // antecedent unsatisfiable
            if (eqs.empty()) continue;                         // identical keys merge upstream

            ExprId ante = eqs.size() == 1
                ? eqs[0]
                : ir_.addShared(CoreExpr{Kind::And, boolS,
                          SmallVector<ExprId, 4>(eqs.begin(), eqs.end()), {}});
            ExprId cons = ir_.addShared(CoreExpr{Kind::Eq, boolS,
                          {readList_[i].second, readList_[j].second}, {}});
            extra_.push_back(ir_.addShared(CoreExpr{Kind::Implies, boolS, {ante, cons}, {}}));
        }
    }
}

bool ReadOnlyArrayElim::run() {
    memo_.clear();
    inProgress_.clear();
    rewritten_.clear();
    extra_.clear();
    readVar_.clear();
    readList_.clear();
    reads_.clear();
    falseEqNodes_.clear();
    freeArrayVars_.clear();
    usedWriteArray_ = false;
    didRewrite_ = false;
    bailed_ = false;

    // Pass 1: identify falsifiable array equalities (write-array mode). Must run
    // before safeToEliminate so its scan can treat those equalities as opaque.
    // Gated SEPARATELY (XOLVER_TARGETED_PP_WRITEARRAY, default-OFF): it is a
    // RELAXATION that suppresses UNSAT, so it regresses array-extensionality
    // UNSAT cases (e.g. QF_AX) and only pays off once the residual NIA is
    // solvable. R1 (store-free) is unaffected when this is off.
    if (std::getenv("XOLVER_TARGETED_PP_WRITEARRAY")) {
        if (!collectFalseEqs()) return false;
    }
    if (!safeToEliminate()) return false;

    for (const auto& [level, eid] : ir_.getScopedAssertions()) {
        rewritten_.emplace_back(level, rewriteRec(eid));
        if (bailed_) return false;
    }
    if (!didRewrite_) return false;
    buildCongruences();

    if (std::getenv("XOLVER_TARGETED_PP_DIAG")) {
        std::fprintf(stderr,
            "[ROAE] reads=%zu congruences=%zu exprTableNow=%zu\n",
            readVar_.size(), extra_.size(), ir_.size());
        std::fflush(stderr);
    }
    return true;
}

void ReadOnlyArrayElim::commit() {
    if (!didRewrite_) return;
    int baseLevel = 0;
    if (!rewritten_.empty()) {
        baseLevel = rewritten_.front().first;
        for (const auto& [lvl, eid] : rewritten_) { (void)eid; if (lvl < baseLevel) baseLevel = lvl; }
    }
    ir_.clearAssertions();
    for (const auto& [level, eid] : rewritten_) {
        ir_.addAssertion(eid, level);
    }
    for (ExprId c : extra_) {
        ir_.addAssertion(c, baseLevel);
    }
    if (std::getenv("XOLVER_TARGETED_PP_DUMP")) {
        for (const auto& [level, eid] : rewritten_) {
            (void)level;
            std::fprintf(stderr, "[ROAE-ASSERT] %s\n",
                         dumpExprToSMT2(eid, ir_).c_str());
        }
        for (ExprId c : extra_)
            std::fprintf(stderr, "[ROAE-CONGR] %s\n", dumpExprToSMT2(c, ir_).c_str());
        std::fflush(stderr);
    }
}

} // namespace xolver
