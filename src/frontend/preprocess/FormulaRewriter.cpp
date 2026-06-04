#include "frontend/preprocess/FormulaRewriter.h"
#include "util/MpqUtils.h"

#include <algorithm>
#include <optional>

namespace xolver {

namespace {

// Read a node as a rational constant, if it is one. Handles both numeric
// representations used in this codebase (ConstInt:int64 or string, ConstReal:
// string or int64) plus a single Neg wrapper over a constant.
std::optional<mpq_class> tryRational(const CoreIr& ir, ExprId e) {
    const CoreExpr& n = ir.get(e);
    switch (n.kind) {
        case Kind::ConstInt: {
            if (auto* i = std::get_if<int64_t>(&n.payload.value)) return mpq_class(*i);
            if (auto* s = std::get_if<std::string>(&n.payload.value)) {
                try { return mpqFromString(*s); } catch (...) { return std::nullopt; }
            }
            return std::nullopt;
        }
        case Kind::ConstReal: {
            if (auto* s = std::get_if<std::string>(&n.payload.value)) {
                try { return mpqFromString(*s); } catch (...) { return std::nullopt; }
            }
            if (auto* i = std::get_if<int64_t>(&n.payload.value)) return mpq_class(*i);
            return std::nullopt;
        }
        case Kind::Neg: {
            if (n.children.size() == 1) {
                if (auto v = tryRational(ir, n.children[0])) return -(*v);
            }
            return std::nullopt;
        }
        default:
            return std::nullopt;
    }
}

} // namespace

std::size_t FormulaRewriter::ConsKeyHash::operator()(const ConsKey& k) const {
    std::size_t h = std::hash<uint16_t>{}(static_cast<uint16_t>(k.kind));
    h ^= std::hash<uint32_t>{}(k.sort) + 0x9e3779b97f4a7c15ULL + (h << 6) + (h >> 2);
    for (ExprId c : k.children) {
        h ^= std::hash<uint32_t>{}(c) + 0x9e3779b97f4a7c15ULL + (h << 6) + (h >> 2);
    }
    // Hash the active payload alternative.
    std::size_t ph = 0;
    if (auto* b = std::get_if<bool>(&k.payload)) ph = std::hash<bool>{}(*b);
    else if (auto* i = std::get_if<int64_t>(&k.payload)) ph = std::hash<int64_t>{}(*i);
    else if (auto* s = std::get_if<std::string>(&k.payload)) ph = std::hash<std::string>{}(*s);
    else if (auto* u = std::get_if<uint64_t>(&k.payload)) ph = std::hash<uint64_t>{}(*u);
    h ^= ph + 0x9e3779b97f4a7c15ULL + (h << 6) + (h >> 2);
    return h;
}

FormulaRewriter::FormulaRewriter(CoreIr& ir, SortId boolSort)
    : ir_(ir), boolSort_(boolSort),
      intSort_(ir.intSortId()), realSort_(ir.realSortId()) {}

FormulaRewriter::Verdict FormulaRewriter::run() {
    memo_.clear();
    cons_.clear();
    rewritten_.clear();
    changed_ = false;
    unsat_ = false;

    for (const auto& [level, eid] : ir_.getScopedAssertions()) {
        ExprId r = rewriteRec(eid);
        if (r != eid) changed_ = true;
        if (isFalse(r)) {
            unsat_ = true;
            return Verdict::Unsat;
        }
        rewritten_.emplace_back(level, r);
    }
    return Verdict::Normal;
}

void FormulaRewriter::commit() {
    if (unsat_) return;
    ir_.clearAssertions();
    for (const auto& [level, e] : rewritten_) {
        // Drop assertions that simplified to the boolean constant true.
        if (isTrue(e)) { changed_ = true; continue; }
        ir_.addAssertion(e, level);
    }
}

ExprId FormulaRewriter::rewrite(ExprId e) { return rewriteRec(e); }

ExprId FormulaRewriter::rewriteRec(ExprId root) {
    if (root == NullExpr) return root;
    if (auto it = memo_.find(root); it != memo_.end()) return it->second;

    // Iterative post-order (two-visit work-stack) to avoid stack overflow on
    // deeply nested terms. simplifyNode()/mk() call ir_.add(), which reallocates
    // CoreIr's exprs_ vector — so all node fields are copied per step before any
    // add. Behavior-identical to the former recursion.
    struct Frame { ExprId e; bool processed; };
    std::vector<Frame> stack;
    stack.push_back({root, false});

    while (!stack.empty()) {
        Frame& frame = stack.back();
        ExprId e = frame.e;
        if (memo_.find(e) != memo_.end()) { stack.pop_back(); continue; }

        if (!frame.processed) {
            frame.processed = true;
            const CoreExpr& node = ir_.get(e);
            if (node.children.empty()) { memo_[e] = e; stack.pop_back(); continue; }
            for (int i = static_cast<int>(node.children.size()) - 1; i >= 0; --i) {
                ExprId c = node.children[i];
                if (c != NullExpr && memo_.find(c) == memo_.end()) stack.push_back({c, false});
            }
            continue;
        }

        stack.pop_back();
        Kind kind;
        SortId sort;
        Payload payload;
        std::vector<ExprId> kids;
        {
            const CoreExpr& node = ir_.get(e);
            kind = node.kind;
            sort = node.sort;
            payload = node.payload;
            kids.reserve(node.children.size());
            for (ExprId c : node.children) kids.push_back(c == NullExpr ? NullExpr : memo_.at(c));
        }
        memo_[e] = simplifyNode(kind, sort, std::move(kids), payload);
    }

    return memo_.at(root);
}

// ---------------------------------------------------------------------------
// node construction
// ---------------------------------------------------------------------------

ExprId FormulaRewriter::mk(Kind kind, SortId sort, std::vector<ExprId> children,
                           Payload payload) {
    ConsKey key{kind, sort, children, payload.value};
    if (auto it = cons_.find(key); it != cons_.end()) return it->second;
    CoreExpr e;
    e.kind = kind;
    e.sort = sort;
    e.children = SmallVector<ExprId, 4>(children.begin(), children.end());
    e.payload = std::move(payload);
    ExprId id = ir_.add(std::move(e));
    cons_.emplace(std::move(key), id);
    return id;
}

ExprId FormulaRewriter::mkBool(bool v) {
    return mk(Kind::ConstBool, boolSort_, {}, Payload(v));
}

ExprId FormulaRewriter::mkIntOrReal(const mpq_class& v, SortId sort) {
    if (sort == realSort_ && realSort_ != NullSort) {
        return mk(Kind::ConstReal, sort, {}, Payload(v.get_str()));
    }
    if (sort == intSort_ && intSort_ != NullSort) {
        if (v.get_den() != 1) return NullExpr;          // not an integer value
        mpz_class num = v.get_num();
        if (!num.fits_slong_p()) return NullExpr;        // refuse oversized literal
        return mk(Kind::ConstInt, sort, {}, Payload(static_cast<int64_t>(num.get_si())));
    }
    return NullExpr;
}

// ---------------------------------------------------------------------------
// queries
// ---------------------------------------------------------------------------

bool FormulaRewriter::isBoolConst(ExprId e, bool& out) const {
    if (e == TrueSentinelExpr)  { out = true;  return true; }
    if (e == FalseSentinelExpr) { out = false; return true; }
    if (e == NullExpr) return false;
    const CoreExpr& n = ir_.get(e);
    if (n.kind == Kind::ConstBool) {
        if (auto* b = std::get_if<bool>(&n.payload.value)) { out = *b; return true; }
    }
    return false;
}

bool FormulaRewriter::isTrue(ExprId e) const { bool b; return isBoolConst(e, b) && b; }
bool FormulaRewriter::isFalse(ExprId e) const { bool b; return isBoolConst(e, b) && !b; }

bool FormulaRewriter::isProvablyBool(ExprId e) const {
    if (e == TrueSentinelExpr || e == FalseSentinelExpr) return true;
    if (e == NullExpr) return false;
    const CoreExpr& n = ir_.get(e);
    if (n.sort == boolSort_ && boolSort_ != NullSort) return true;
    auto sk = ir_.sortKind(n.sort);
    if (sk && *sk == SortKind::Bool) return true;
    switch (n.kind) {
        case Kind::Not: case Kind::And: case Kind::Or:
        case Kind::Implies: case Kind::Xor: case Kind::ConstBool:
        case Kind::Eq: case Kind::Distinct:
        case Kind::Lt: case Kind::Leq: case Kind::Gt: case Kind::Geq:
        case Kind::IsInt:
            return true;
        default:
            return false;
    }
}

ExprId FormulaRewriter::negate(ExprId e) {
    bool b;
    if (isBoolConst(e, b)) return mkBool(!b);
    const CoreExpr& n = ir_.get(e);
    if (n.kind == Kind::Not && n.children.size() == 1) return n.children[0];
    return mk(Kind::Not, n.sort, {e}, Payload());
}

// ---------------------------------------------------------------------------
// the simplifier
// ---------------------------------------------------------------------------

ExprId FormulaRewriter::simplifyNode(Kind kind, SortId sort,
                                     std::vector<ExprId> children,
                                     const Payload& payload) {
    switch (kind) {
        // ---------------- Boolean ----------------
        case Kind::Not: {
            if (children.size() != 1) break;
            return negate(children[0]);
        }
        case Kind::And:
        case Kind::Or: {
            const bool isAnd = (kind == Kind::And);
            // Flatten one level (children already flattened bottom-up).
            std::vector<ExprId> flat;
            flat.reserve(children.size());
            for (ExprId c : children) {
                const CoreExpr& cn = ir_.get(c);
                if (cn.kind == kind) {
                    for (ExprId gc : cn.children) flat.push_back(gc);
                } else {
                    flat.push_back(c);
                }
            }
            // Dedup + dominator/identity handling + complementary detection.
            std::vector<ExprId> kept;
            std::unordered_map<ExprId, bool> seen;   // value: present
            for (ExprId c : flat) {
                bool b;
                if (isBoolConst(c, b)) {
                    // AND: drop true, false dominates. OR: drop false, true dominates.
                    if (b == isAnd) continue;          // identity element → drop
                    return mkBool(!isAnd);             // dominator → ⊥ for AND, ⊤ for OR
                }
                if (seen.count(c)) continue;           // dedup
                // complementary literal already kept?
                ExprId neg = negate(c);
                if (seen.count(neg)) {
                    return mkBool(!isAnd);             // x ∧ ¬x → ⊥ ; x ∨ ¬x → ⊤
                }
                seen[c] = true;
                kept.push_back(c);
            }
            if (kept.empty()) return mkBool(isAnd);    // empty AND → ⊤, empty OR → ⊥
            if (kept.size() == 1) return kept[0];
            return mk(kind, sort, std::move(kept), Payload());
        }
        case Kind::Implies: {
            if (children.size() != 2) break;
            ExprId a = children[0], b = children[1];
            if (isFalse(a)) return mkBool(true);
            if (isTrue(b))  return mkBool(true);
            if (isTrue(a))  return b;
            if (isFalse(b)) return negate(a);
            if (a == b)     return mkBool(true);
            return mk(kind, sort, std::move(children), Payload());
        }
        case Kind::Xor: {
            if (children.size() != 2) break;
            ExprId a = children[0], b = children[1];
            bool ba, bb;
            bool ca = isBoolConst(a, ba), cb = isBoolConst(b, bb);
            if (ca && cb) return mkBool(ba != bb);
            if (a == b)   return mkBool(false);
            if (ca) return ba ? negate(b) : b;         // (xor true b)→¬b ; (xor false b)→b
            if (cb) return bb ? negate(a) : a;
            // (xor a ¬a) → ⊤
            if (negate(a) == b) return mkBool(true);
            return mk(kind, sort, std::move(children), Payload());
        }
        case Kind::Ite: {
            if (children.size() != 3) break;
            ExprId c = children[0], t = children[1], f = children[2];
            if (isTrue(c))  return t;
            if (isFalse(c)) return f;
            if (t == f)     return t;
            bool bt, bf;
            bool ct = isBoolConst(t, bt), cf = isBoolConst(f, bf);
            if (ct && cf) {
                if (bt && !bf) return c;               // ite(c,⊤,⊥) → c
                if (!bt && bf) return negate(c);       // ite(c,⊥,⊤) → ¬c
            }
            return mk(kind, sort, std::move(children), Payload());
        }

        // ---------------- Eq / Distinct ----------------
        case Kind::Eq: {
            if (children.size() < 2) break;
            // Reflexivity: all syntactically identical → true.
            bool allEq = true;
            for (size_t i = 1; i < children.size(); ++i)
                if (children[i] != children[0]) { allEq = false; break; }
            if (allEq) return mkBool(true);
            if (children.size() == 2) {
                ExprId a = children[0], b = children[1];
                // Numeric-constant equality.
                auto va = tryRational(ir_, a), vb = tryRational(ir_, b);
                if (va && vb) return mkBool(*va == *vb);
                // Shared-Add-term cancellation: `(= (+ X1 X2 ...) (+ Y1 Y2 ...))`
                // simplifies by removing the intersection of the two operand
                // multisets. Sound: subtracting the same value from both sides
                // preserves equality. Closes the "semi-magic square of cubes"
                // chain (MathProblems SC_02 etc.) where, after SOLVE_EQS removes
                // `t`, the asserted formula becomes
                //   (= (+ x_00^3 x_01^3) (+ x_00^3 x_10^3))
                // which collapses to `(= x_01^3 x_10^3)` and then, via the
                // odd-power injection below, to `(= x_01 x_10)` -- contradicting
                // (distinct x_01 x_10).
                const CoreExpr& an = ir_.get(a);
                const CoreExpr& bn = ir_.get(b);
                if (an.kind == Kind::Add && bn.kind == Kind::Add &&
                    an.children.size() >= 2 && bn.children.size() >= 2) {
                    std::vector<ExprId> la, rb;
                    la.reserve(an.children.size());
                    rb.reserve(bn.children.size());
                    for (size_t i = 0; i < an.children.size(); ++i) la.push_back(an.children[i]);
                    for (size_t i = 0; i < bn.children.size(); ++i) rb.push_back(bn.children[i]);
                    bool cancelled = false;
                    for (auto it = la.begin(); it != la.end(); ) {
                        auto match = std::find(rb.begin(), rb.end(), *it);
                        if (match != rb.end()) {
                            rb.erase(match);
                            it = la.erase(it);
                            cancelled = true;
                        } else {
                            ++it;
                        }
                    }
                    if (cancelled) {
                        auto rebuild = [&](std::vector<ExprId>& v, SortId sortArith) -> ExprId {
                            if (v.empty()) {
                                return mkIntOrReal(mpq_class(0), sortArith);
                            }
                            if (v.size() == 1) return v[0];
                            return mk(Kind::Add, sortArith, v, Payload());
                        };
                        ExprId newA = rebuild(la, an.sort);
                        ExprId newB = rebuild(rb, bn.sort);
                        if (newA != NullExpr && newB != NullExpr && (newA != a || newB != b)) {
                            return mk(Kind::Eq, sort, {newA, newB}, Payload());
                        }
                    }
                }
                // Boolean iff identities (only when provably bool).
                if (isProvablyBool(a) && isProvablyBool(b)) {
                    bool ba, bb;
                    if (isBoolConst(a, ba)) return ba ? b : negate(b);
                    if (isBoolConst(b, bb)) return bb ? a : negate(a);
                }
                // Odd-power injection (sound over Z): if both sides are pow(_, k)
                // with the SAME odd positive integer constant k, rewrite to
                // (= base_a base_b). x^k is injective over Z for odd k, so
                // x^k = y^k ↔ x = y. For even k the rule is unsound (x^2 = y^2
                // doesn't imply x = y -- could differ in sign). Only fires on
                // Int-sorted exponents read from a ConstInt payload; non-constant
                // or even / negative exponents fall through unchanged.
                //
                // Closes the "semi-magic square of cubes" pattern (MathProblems
                // SC_02 etc.) where the constraint chain collapses to
                // x_10^3 = x_01^3 -> x_10 = x_01, contradicting (distinct ...).
                auto isPowOdd = [&](ExprId eid, ExprId& base, mpz_class& expOut) -> bool {
                    const CoreExpr& e = ir_.get(eid);
                    // Explicit Pow(base, k).
                    if (e.kind == Kind::Pow && e.children.size() == 2) {
                        const CoreExpr& exp = ir_.get(e.children[1]);
                        if (exp.kind != Kind::ConstInt) return false;
                        if (auto* i = std::get_if<int64_t>(&exp.payload.value)) {
                            if (*i <= 0 || (*i % 2) == 0) return false;
                            expOut = mpz_class(*i);
                        } else if (auto* s = std::get_if<std::string>(&exp.payload.value)) {
                            try { expOut = mpz_class(*s); }
                            catch (...) { return false; }
                            if (expOut <= 0 || (expOut % 2) == 0) return false;
                        } else {
                            return false;
                        }
                        base = e.children[0];
                        return true;
                    }
                    // Implicit repeated-var Mul: (* x x x ...) with N ≥ 3 odd
                    // and ALL children syntactically equal to one ExprId.
                    // SMT-LIB writes `x^3` as `(* x x x)`; the rule must catch
                    // both forms. N must be odd.
                    if (e.kind == Kind::Mul && e.children.size() >= 3) {
                        ExprId first = e.children[0];
                        for (size_t i = 1; i < e.children.size(); ++i)
                            if (e.children[i] != first) return false;
                        size_t n = e.children.size();
                        if ((n & 1) == 0) return false;        // even -> not injective
                        base = first;
                        expOut = mpz_class(static_cast<unsigned long>(n));
                        return true;
                    }
                    return false;
                };
                ExprId baseA = NullExpr, baseB = NullExpr;
                mpz_class expA, expB;
                if (isPowOdd(a, baseA, expA) && isPowOdd(b, baseB, expB) && expA == expB) {
                    // Reflexive shortcut: a^k = a^k → true.
                    if (baseA == baseB) return mkBool(true);
                    // Build (= baseA baseB) as a fresh node; the fixpoint loop
                    // in run() will further-simplify it (e.g. against a
                    // (distinct baseA baseB) atom elsewhere).
                    return mk(Kind::Eq, sort, {baseA, baseB}, Payload());
                }
            }
            return mk(kind, sort, std::move(children), Payload());
        }
        case Kind::Distinct: {
            if (children.size() < 2) {
                return mkBool(true);                   // distinct of <2 args is vacuously true
            }
            // Any two syntactically identical → false.
            for (size_t i = 0; i < children.size(); ++i)
                for (size_t j = i + 1; j < children.size(); ++j)
                    if (children[i] == children[j]) return mkBool(false);
            if (children.size() == 2) {
                auto va = tryRational(ir_, children[0]), vb = tryRational(ir_, children[1]);
                if (va && vb) return mkBool(*va != *vb);
                if (isProvablyBool(children[0]) && isProvablyBool(children[1])) {
                    bool b0, b1;
                    if (isBoolConst(children[0], b0)) return b0 ? negate(children[1]) : children[1];
                    if (isBoolConst(children[1], b1)) return b1 ? negate(children[0]) : children[0];
                }
            }
            return mk(kind, sort, std::move(children), Payload());
        }

        // ---------------- Relational (const eval only) ----------------
        case Kind::Lt: case Kind::Leq: case Kind::Gt: case Kind::Geq: {
            if (children.size() == 2) {
                auto va = tryRational(ir_, children[0]), vb = tryRational(ir_, children[1]);
                if (va && vb) {
                    bool r = false;
                    switch (kind) {
                        case Kind::Lt:  r = (*va <  *vb); break;
                        case Kind::Leq: r = (*va <= *vb); break;
                        case Kind::Gt:  r = (*va >  *vb); break;
                        case Kind::Geq: r = (*va >= *vb); break;
                        default: break;
                    }
                    return mkBool(r);
                }
            }
            return mk(kind, sort, std::move(children), Payload());
        }

        // ---------------- Arithmetic ----------------
        case Kind::Neg: {
            if (children.size() != 1) break;
            ExprId a = children[0];
            const CoreExpr& an = ir_.get(a);
            if (an.kind == Kind::Neg && an.children.size() == 1) return an.children[0]; // -(-x)→x
            if (auto v = tryRational(ir_, a)) {
                ExprId folded = mkIntOrReal(-(*v), sort);
                if (folded != NullExpr) return folded;
            }
            return mk(kind, sort, std::move(children), Payload());
        }
        case Kind::Add: {
            if (children.empty()) break;
            std::vector<ExprId> flat;
            for (ExprId c : children) {
                const CoreExpr& cn = ir_.get(c);
                if (cn.kind == Kind::Add) for (ExprId gc : cn.children) flat.push_back(gc);
                else flat.push_back(c);
            }
            mpq_class constSum = 0;
            std::vector<ExprId> terms;
            for (ExprId c : flat) {
                if (auto v = tryRational(ir_, c)) constSum += *v;
                else terms.push_back(c);
            }
            if (terms.empty()) {
                ExprId folded = mkIntOrReal(constSum, sort);
                if (folded != NullExpr) return folded;
                // could not represent the constant — fall through to rebuild
            } else {
                if (constSum != 0) {
                    ExprId cterm = mkIntOrReal(constSum, sort);
                    if (cterm != NullExpr) terms.push_back(cterm);
                    else return mk(kind, sort, std::move(children), Payload()); // bail safely
                }
                if (terms.size() == 1) return terms[0];
                return mk(kind, sort, std::move(terms), Payload());
            }
            return mk(kind, sort, std::move(children), Payload());
        }
        case Kind::Sub: {
            // SMT-LIB n-ary `(- a b c ...)` = `((a-b)-c) - ...`. Old code
            // only handled size == 2 (and silently passed n >= 3 through
            // unrewritten). Now folds n-ary by collapsing all constant
            // operands into a running scalar.
            if (children.empty()) break;
            if (children.size() == 1) {
                // `(- a)` = -a (unary form).
                ExprId a = children[0];
                if (auto va = tryRational(ir_, a)) {
                    ExprId folded = mkIntOrReal(-*va, sort);
                    if (folded != NullExpr) return folded;
                }
                return mk(Kind::Neg, sort, std::move(children), Payload());
            }
            if (children.size() == 2) {
                ExprId a = children[0], b = children[1];
                auto va = tryRational(ir_, a), vb = tryRational(ir_, b);
                if (va && vb) {
                    ExprId folded = mkIntOrReal(*va - *vb, sort);
                    if (folded != NullExpr) return folded;
                }
                if (vb && *vb == 0) return a;          // x − 0 → x
                return mk(kind, sort, std::move(children), Payload());
            }
            // n-ary (n >= 3): fold constants from positions ≥ 1 into a
            // running scalar; preserve non-constants in order.
            mpq_class subConst(0);
            std::vector<ExprId> nonConst{children[0]};  // first arg untouched
            bool anyFolded = false;
            for (size_t i = 1; i < children.size(); ++i) {
                if (auto v = tryRational(ir_, children[i])) {
                    subConst += *v;
                    anyFolded = true;
                } else {
                    nonConst.push_back(children[i]);
                }
            }
            if (anyFolded) {
                if (subConst != 0) {
                    ExprId cterm = mkIntOrReal(subConst, sort);
                    if (cterm != NullExpr) nonConst.push_back(cterm);
                    else return mk(kind, sort, std::move(children), Payload());
                }
                if (nonConst.size() == 1) {
                    // First arg minus nothing (all constants were zero).
                    if (auto v0 = tryRational(ir_, nonConst[0])) {
                        ExprId folded = mkIntOrReal(*v0, sort);
                        if (folded != NullExpr) return folded;
                    }
                    return nonConst[0];
                }
                return mk(kind, sort, std::move(nonConst), Payload());
            }
            return mk(kind, sort, std::move(children), Payload());
        }
        case Kind::Mul: {
            if (children.empty()) break;
            std::vector<ExprId> flat;
            for (ExprId c : children) {
                const CoreExpr& cn = ir_.get(c);
                if (cn.kind == Kind::Mul) for (ExprId gc : cn.children) flat.push_back(gc);
                else flat.push_back(c);
            }
            mpq_class constProd = 1;
            std::vector<ExprId> terms;
            for (ExprId c : flat) {
                if (auto v = tryRational(ir_, c)) constProd *= *v;
                else terms.push_back(c);
            }
            if (constProd == 0) {
                // x * 0 → 0 (Mul is total in SMT arithmetic).
                ExprId zero = mkIntOrReal(mpq_class(0), sort);
                if (zero != NullExpr) return zero;
                return mk(kind, sort, std::move(children), Payload());
            }
            if (terms.empty()) {
                ExprId folded = mkIntOrReal(constProd, sort);
                if (folded != NullExpr) return folded;
            } else {
                if (constProd != 1) {
                    ExprId cterm = mkIntOrReal(constProd, sort);
                    if (cterm != NullExpr) terms.insert(terms.begin(), cterm);
                    else return mk(kind, sort, std::move(children), Payload());
                }
                if (terms.size() == 1) return terms[0];
                return mk(kind, sort, std::move(terms), Payload());
            }
            return mk(kind, sort, std::move(children), Payload());
        }

        default:
            break;
    }
    // Default: rebuild structurally (hash-consed). Preserves semantics.
    return mk(kind, sort, std::move(children), payload);
}

} // namespace xolver
