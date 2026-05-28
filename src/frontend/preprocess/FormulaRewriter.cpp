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
                // Boolean iff identities (only when provably bool).
                if (isProvablyBool(a) && isProvablyBool(b)) {
                    bool ba, bb;
                    if (isBoolConst(a, ba)) return ba ? b : negate(b);
                    if (isBoolConst(b, bb)) return bb ? a : negate(a);
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
            if (children.size() != 2) break;
            ExprId a = children[0], b = children[1];
            auto va = tryRational(ir_, a), vb = tryRational(ir_, b);
            if (va && vb) {
                ExprId folded = mkIntOrReal(*va - *vb, sort);
                if (folded != NullExpr) return folded;
            }
            if (vb && *vb == 0) return a;              // x − 0 → x
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
