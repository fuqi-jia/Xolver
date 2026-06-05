#include "frontend/preprocess/IntDivModConstantFold.h"
#include <cstdio>
#include <cstdlib>
#include <gmpxx.h>
#include <optional>
#include <vector>
#include <string>

namespace xolver {

IntDivModConstantFold::IntDivModConstantFold(CoreIr& ir)
    : ir_(ir), intSortId_(ir.intSortId()) {}

bool IntDivModConstantFold::run() {
    memo_.clear();
    folded_.clear();
    didFold_ = false;

    for (const auto& [level, eid] : ir_.getScopedAssertions()) {
        ExprId rewritten = foldRec(eid);
        folded_.emplace_back(level, rewritten);
    }
    return true;
}

void IntDivModConstantFold::commit() {
    if (!didFold_) return;
    ir_.clearAssertions();
    for (const auto& [level, eid] : folded_) {
        ir_.addAssertion(eid, level);
    }
}

ExprId IntDivModConstantFold::foldRec(ExprId root) {
    if (auto it = memo_.find(root); it != memo_.end()) return it->second;

    // Iterative post-order (two-visit work-stack) to avoid stack overflow on
    // deeply nested terms. Behavior-identical to the former recursion.
    struct Frame { ExprId e; bool processed; };
    std::vector<Frame> stack;
    stack.push_back({root, false});

    while (!stack.empty()) {
        Frame& frame = stack.back();
        ExprId e = frame.e;
        if (memo_.find(e) != memo_.end()) { stack.pop_back(); continue; }

        const auto node = ir_.get(e);  // value copy: tryFoldDivMod/ir_.add may relocate

        if (!frame.processed) {
            frame.processed = true;
            if (node.children.empty()) { memo_[e] = e; stack.pop_back(); continue; }
            for (int i = static_cast<int>(node.children.size()) - 1; i >= 0; --i) {
                ExprId c = node.children[i];
                if (memo_.find(c) == memo_.end()) stack.push_back({c, false});
            }
            continue;
        }

        stack.pop_back();
        SmallVector<ExprId, 4> newChildren;
        bool changed = false;
        for (ExprId c : node.children) {
            ExprId rc = memo_.at(c);
            if (rc != c) changed = true;
            newChildren.push_back(rc);
        }
        ExprId rebuilt = e;
        if (changed) {
            CoreExpr fresh;
            fresh.kind = node.kind;
            fresh.sort = node.sort;
            fresh.children = std::move(newChildren);
            fresh.payload = node.payload;
            rebuilt = ir_.add(std::move(fresh));
        }
        // Try div/mod constant fold, then the symbolic-modulus law for non-const M.
        ExprId folded = tryFoldDivMod(rebuilt);
        if (folded == rebuilt) folded = trySymbolicModSimplify(rebuilt);
        if (folded != rebuilt) didFold_ = true;
        memo_[e] = folded;
    }

    return memo_.at(root);
}

namespace {

std::optional<mpz_class> extractIntConst(const CoreExpr& n) {
    if (n.kind == Kind::ConstInt) {
        if (auto* v = std::get_if<int64_t>(&n.payload.value)) return mpz_class(*v);
        return std::nullopt;
    }
    if (n.kind == Kind::ConstReal) {
        // Defensive: the parser may carry int-valued literals via ConstReal.
        if (auto* s = std::get_if<std::string>(&n.payload.value)) {
            mpq_class q(*s);
            if (q.get_den() == 1) return mpz_class(q.get_num());
        }
        return std::nullopt;
    }
    return std::nullopt;
}

// SMT-LIB integer div/mod (euclidean): given a, b with b != 0,
//   q = sign(b) * floor(a / |b|)   if b > 0:  q = floor(a/b)
//                                    if b < 0:  q = -floor(a/|b|)
//   r = a - b * q,   guaranteed 0 <= r < |b|.
std::pair<mpz_class, mpz_class> smtlibDivMod(const mpz_class& a, const mpz_class& b) {
    mpz_class absB = abs(b);
    // floor division of a by absB, returning q', r' with 0 <= r' < absB.
    mpz_class qAbs;
    mpz_class rAbs;
    mpz_fdiv_qr(qAbs.get_mpz_t(), rAbs.get_mpz_t(), a.get_mpz_t(), absB.get_mpz_t());
    // rAbs in [0, absB)
    mpz_class q = (b > 0) ? qAbs : -qAbs;
    mpz_class r = rAbs;
    return {q, r};
}

} // namespace

ExprId IntDivModConstantFold::tryFoldDivMod(ExprId e) {
    const auto& node = ir_.get(e);
    if (node.sort != intSortId_) return e;
    if (node.kind != Kind::Div && node.kind != Kind::Mod) return e;
    if (node.children.size() != 2) return e;
    auto a = extractIntConst(ir_.get(node.children[0]));
    auto b = extractIntConst(ir_.get(node.children[1]));
    if (!a || !b) return e;
    if (*b == 0) return e;  // leave for IntDivModLowerer's undef branch.

    auto [q, r] = smtlibDivMod(*a, *b);
    const mpz_class& value = (node.kind == Kind::Div) ? q : r;
    if (!value.fits_slong_p()) return e;  // refuse oversized literals.
    return mkConstInt(value.get_si());
}

ExprId IntDivModConstantFold::mkMul2(ExprId a, ExprId b) {
    CoreExpr m; m.kind = Kind::Mul; m.sort = intSortId_;
    m.children.push_back(a); m.children.push_back(b);
    return cons(std::move(m));
}

ExprId IntDivModConstantFold::mkMod2(ExprId a, ExprId M) {
    CoreExpr m; m.kind = Kind::Mod; m.sort = intSortId_;
    m.children.push_back(a); m.children.push_back(M);
    return cons(std::move(m));
}

ExprId IntDivModConstantFold::mkIte3(ExprId c, ExprId a, ExprId b) {
    if (a == b) return a;  // identical-branch collapse
    CoreExpr e; e.kind = Kind::Ite; e.sort = intSortId_;
    e.children.push_back(c); e.children.push_back(a); e.children.push_back(b);
    return cons(std::move(e));
}

// True iff `e` is an integer constant equal to `want` — robust to the parser
// carrying int-valued literals via ConstReal (see extractIntConst's note), which
// is why `(* x 1)` failed to fold and broke hash-cons canonicalization.
static bool isIntConstEq(const CoreExpr& n, int64_t want) {
    if (n.kind == Kind::ConstInt) {
        if (auto* v = std::get_if<int64_t>(&n.payload.value)) return *v == want;
    } else if (n.kind == Kind::ConstReal) {
        if (auto* s = std::get_if<std::string>(&n.payload.value)) {
            mpq_class q(*s);
            return q.get_den() == 1 && q.get_num() == want;
        }
    }
    return false;
}

ExprId IntDivModConstantFold::simplifyMul(const std::vector<ExprId>& factors) {
    std::vector<ExprId> kept;
    for (ExprId f : factors) {
        const auto& fn = ir_.get(f);
        if (isIntConstEq(fn, 0)) return mkConstInt(0);
        if (isIntConstEq(fn, 1)) continue;
        kept.push_back(f);
    }
    if (kept.empty()) return mkConstInt(1);
    ExprId r = kept[0];
    for (size_t i = 1; i < kept.size(); ++i) r = mkMul2(r, kept[i]);
    return r;
}

ExprId IntDivModConstantFold::distribute(ExprId e) {
    const auto& n = ir_.get(e);
    if (n.kind == Kind::Add || n.kind == Kind::Sub) {
        SmallVector<ExprId, 4> nc; bool ch = false;
        for (ExprId c : n.children) { ExprId d = distribute(c); if (d != c) ch = true; nc.push_back(d); }
        if (!ch) return e;
        CoreExpr f; f.kind = n.kind; f.sort = n.sort; f.children = std::move(nc); f.payload = n.payload;
        return ir_.add(std::move(f));
    }
    if (n.kind == Kind::Neg && n.children.size() == 1) {
        ExprId d = distribute(n.children[0]);
        if (d == n.children[0]) return e;
        CoreExpr f; f.kind = Kind::Neg; f.sort = n.sort; f.children.push_back(d);
        return ir_.add(std::move(f));
    }
    if (n.kind == Kind::Mul && n.children.size() == 2) {
        ExprId a = distribute(n.children[0]);
        ExprId b = distribute(n.children[1]);
        auto distOver = [&](ExprId factor, ExprId sumId, bool factorLeft) -> ExprId {
            const auto& sn = ir_.get(sumId);
            CoreExpr f; f.kind = sn.kind; f.sort = intSortId_; f.payload = sn.payload;
            for (ExprId si : sn.children) {
                ExprId prod = factorLeft ? mkMul2(factor, si) : mkMul2(si, factor);
                f.children.push_back(distribute(prod));
            }
            return ir_.add(std::move(f));
        };
        const auto& bn = ir_.get(b);
        if (bn.kind == Kind::Add || bn.kind == Kind::Sub) return distOver(a, b, true);
        const auto& an = ir_.get(a);
        if (an.kind == Kind::Add || an.kind == Kind::Sub) return distOver(b, a, false);
        if (a == n.children[0] && b == n.children[1]) return e;
        return mkMul2(a, b);
    }
    return e;
}

void IntDivModConstantFold::collectAddSub(
    ExprId e, bool neg, std::vector<std::pair<ExprId, bool>>& out) const {
    const auto& n = ir_.get(e);
    if (n.kind == Kind::Add) { for (ExprId c : n.children) collectAddSub(c, neg, out); return; }
    if (n.kind == Kind::Sub) {
        if (n.children.size() == 1) { collectAddSub(n.children[0], !neg, out); return; }
        for (size_t i = 0; i < n.children.size(); ++i)
            collectAddSub(n.children[i], i == 0 ? neg : !neg, out);
        return;
    }
    if (n.kind == Kind::Neg && n.children.size() == 1) { collectAddSub(n.children[0], !neg, out); return; }
    if (isIntConstEq(n, 0)) return;  // 0 additive term contributes nothing
    out.push_back({e, neg});
}

bool IntDivModConstantFold::termHasFactor(ExprId t, ExprId M) const {
    if (t == M) return true;
    const auto& n = ir_.get(t);
    if (n.kind == Kind::Mul) { for (ExprId c : n.children) if (termHasFactor(c, M)) return true; }
    else if (n.kind == Kind::Neg && n.children.size() == 1) return termHasFactor(n.children[0], M);
    return false;
}

ExprId IntDivModConstantFold::mkAddN(const std::vector<ExprId>& ts) {
    if (ts.size() == 1) return ts[0];
    CoreExpr a; a.kind = Kind::Add; a.sort = intSortId_;
    for (ExprId t : ts) a.children.push_back(t);
    return cons(std::move(a));
}

ExprId IntDivModConstantFold::rebuildAddSub(
    const std::vector<std::pair<ExprId, bool>>& terms) {
    if (terms.empty()) return mkConstInt(0);
    auto fold1 = [&](ExprId t) -> ExprId {
        const auto& tn = ir_.get(t);
        if (tn.kind != Kind::Mul) return t;
        std::vector<ExprId> fs(tn.children.begin(), tn.children.end());
        return simplifyMul(fs);
    };
    std::vector<ExprId> pos, neg;
    for (const auto& [t, ng] : terms) (ng ? neg : pos).push_back(fold1(t));
    ExprId posSum = pos.empty() ? mkConstInt(0) : mkAddN(pos);
    if (neg.empty()) return posSum;
    ExprId negSum = mkAddN(neg);
    CoreExpr s; s.kind = Kind::Sub; s.sort = intSortId_;
    s.children.push_back(posSum); s.children.push_back(negSum);
    return cons(std::move(s));
}

ExprId IntDivModConstantFold::trySymbolicModSimplify(ExprId e, int depth) {
    const auto& node = ir_.get(e);
    if (node.kind != Kind::Mod || node.children.size() != 2) return e;
    if (node.sort != intSortId_) return e;
    if (depth > 16) return e;  // blowup backstop (nested-ite duplication)
    ExprId p = node.children[0];
    ExprId M = node.children[1];
    const auto& mn = ir_.get(M);
    if (mn.kind == Kind::ConstInt || mn.kind == Kind::ConstReal) return e;

    // Distribute products over sums, then collect additive monomials (0-skipped).
    ExprId pd = distribute(p);
    std::vector<std::pair<ExprId, bool>> terms;
    collectAddSub(pd, false, terms);

    // ITE-LIFT + MOD-OVER-ITE: pull the first additive `(ite C a b)` term out of
    // the mod, distributing the mod into both branches. Reaches the mods nested
    // inside intmodtotal's ite(M=0,..) that block the flat drop. Identity, sound.
    for (size_t i = 0; i < terms.size(); ++i) {
        const auto& tn = ir_.get(terms[i].first);
        if (tn.kind != Kind::Ite || tn.children.size() != 3) continue;
        ExprId C = tn.children[0], a = tn.children[1], b = tn.children[2];
        auto branchMod = [&](ExprId br) -> ExprId {
            auto ts = terms;
            ts[i].first = br;                       // replace the ite by its branch
            ExprId pBr = rebuildAddSub(ts);
            return trySymbolicModSimplify(mkMod2(pBr, M), depth + 1);
        };
        return mkIte3(C, branchMod(a), branchMod(b));  // collapses if branches equal
    }

    // No ite term: drop every monomial divisible by M; collapse a lone (mod a M).
    std::vector<std::pair<ExprId, bool>> kept;
    bool dropped = false;
    for (const auto& tn : terms) {
        if (termHasFactor(tn.first, M)) { dropped = true; continue; }
        kept.push_back(tn);
    }
    if (kept.size() == 1 && !kept[0].second) {
        const auto& kn = ir_.get(kept[0].first);
        if (kn.kind == Kind::Mod && kn.children.size() == 2 && kn.children[1] == M)
            return kept[0].first;  // idempotence (incl. intadd(0,·) wrapper)
    }
    (void)dropped;
    // CANONICALIZE the argument ALWAYS (not only on a drop): rebuildAddSub is a
    // deterministic function of the monomial multiset, so two arguments that are
    // equal modulo M — e.g. the dropped `x*(M-1)` reducing to `-x`, and a literal
    // `(- 0 x)` on the other side of the goal — produce the SAME ExprId and the
    // two mods become syntactically identical (hash-cons), which is what lets the
    // theory's ite case-split close it (proven by skel_simp). Scoped to
    // non-constant M, so ordinary constant-modulus mods are untouched.
    ExprId p2 = rebuildAddSub(kept);
    if (const auto& p2n = ir_.get(p2); p2n.kind == Kind::ConstInt) {
        if (auto* v = std::get_if<int64_t>(&p2n.payload.value); v && *v == 0) return mkConstInt(0);
    }
    return mkMod2(p2, M);
}

ExprId IntDivModConstantFold::cons(CoreExpr e) {
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

ExprId IntDivModConstantFold::mkConstInt(int64_t v) {
    CoreExpr e;
    e.kind = Kind::ConstInt;
    e.sort = intSortId_;
    e.payload = Payload(v);
    return cons(std::move(e));
}

} // namespace xolver
