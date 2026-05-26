#include "frontend/preprocess/ModularConsistencyChecker.h"

namespace zolver {

namespace {

// Extract an integer constant from a node. SOMTParser canonicalizes some
// integer literals as Kind::ConstReal with a rational-string payload whose
// denominator is 1 (sort is IntOrReal). We accept those alongside the
// proper Kind::ConstInt encoding so the matcher works in both QF_NIA and
// QF_LIA inputs interchangeably.
std::optional<mpz_class> extractIntConst(const CoreIr& ir, ExprId e) {
    const auto& node = ir.get(e);
    if (node.kind == Kind::ConstInt) {
        if (auto* v = std::get_if<int64_t>(&node.payload.value)) {
            return mpz_class(*v);
        }
        return std::nullopt;
    }
    if (node.kind == Kind::ConstReal) {
        if (auto* s = std::get_if<std::string>(&node.payload.value)) {
            try {
                mpq_class q(*s);
                if (q.get_den() == 1) return mpz_class(q.get_num());
            } catch (...) {
                // fallthrough
            }
        }
        return std::nullopt;
    }
    if (node.kind == Kind::Neg && node.children.size() == 1) {
        if (auto v = extractIntConst(ir, node.children[0])) return -(*v);
    }
    return std::nullopt;
}

} // namespace

ModularConsistencyChecker::ModularConsistencyChecker(CoreIr& ir)
    : ir_(ir),
      boolSortId_(ir.boolSortId()),
      intSortId_(ir.intSortId()) {}

std::optional<ModularConsistencyChecker::ModConstraint>
ModularConsistencyChecker::matchModEq(ExprId assertion, ScopeLevel level) {
    const auto& node = ir_.get(assertion);
    if (node.kind != Kind::Eq) return std::nullopt;
    if (node.children.size() != 2) return std::nullopt;

    auto tryMatch = [&](ExprId modCand, ExprId constCand) -> std::optional<ModConstraint> {
        const auto& mn = ir_.get(modCand);
        if (mn.kind != Kind::Mod) return std::nullopt;
        if (mn.children.size() != 2) return std::nullopt;
        const auto& varN = ir_.get(mn.children[0]);
        if (varN.kind != Kind::Variable) return std::nullopt;
        auto modV = extractIntConst(ir_, mn.children[1]);
        auto resV = extractIntConst(ir_, constCand);
        if (!modV || !resV) return std::nullopt;
        // Require the modulus to be a positive integer; zero/negative divisors
        // are out of scope for this pass (the lowerer handles those).
        if (*modV <= 0) return std::nullopt;
        ModConstraint mc;
        mc.varExpr       = mn.children[0];
        mc.modulus       = *modV;
        mc.residue       = *resV;
        mc.origAssertion = assertion;
        mc.level         = level;
        return mc;
    };

    if (auto r = tryMatch(node.children[0], node.children[1])) return r;
    if (auto r = tryMatch(node.children[1], node.children[0])) return r;
    return std::nullopt;
}

bool ModularConsistencyChecker::matchBound(
    ExprId assertion, ScopeLevel level,
    std::unordered_map<ExprId, VarBounds>& bounds) {

    const auto& node = ir_.get(assertion);
    Kind rel = node.kind;
    if (rel != Kind::Geq && rel != Kind::Leq &&
        rel != Kind::Gt  && rel != Kind::Lt  &&
        rel != Kind::Eq) {
        return false;
    }
    if (node.children.size() != 2) return false;

    const auto& c0 = ir_.get(node.children[0]);
    const auto& c1 = ir_.get(node.children[1]);

    ExprId varSide;
    bool reversed = false;
    std::optional<mpz_class> cOpt;
    if (c0.kind == Kind::Variable) {
        cOpt = extractIntConst(ir_, node.children[1]);
        if (cOpt) varSide = node.children[0];
    } else if (c1.kind == Kind::Variable) {
        cOpt = extractIntConst(ir_, node.children[0]);
        if (cOpt) {
            varSide  = node.children[1];
            reversed = true;
        }
    }
    if (!cOpt) return false;

    // Only integer-sorted variables.
    if (ir_.get(varSide).sort != intSortId_) return false;

    mpz_class c = *cOpt;
    auto& vb = bounds[varSide];
    vb.level = level;

    // After accounting for `reversed`, treat as `var REL c`.
    Kind effRel = rel;
    if (reversed) {
        switch (rel) {
            case Kind::Geq: effRel = Kind::Leq; break;
            case Kind::Leq: effRel = Kind::Geq; break;
            case Kind::Gt:  effRel = Kind::Lt;  break;
            case Kind::Lt:  effRel = Kind::Gt;  break;
            case Kind::Eq:  effRel = Kind::Eq;  break;
            default: break;
        }
    }

    auto tightenLo = [&](const mpz_class& newLo) {
        if (!vb.lo || newLo > *vb.lo) vb.lo = newLo;
    };
    auto tightenHi = [&](const mpz_class& newHi) {
        if (!vb.hi || newHi < *vb.hi) vb.hi = newHi;
    };

    // Convert strict bounds to inclusive (var integer).
    switch (effRel) {
        case Kind::Geq: tightenLo(c); break;
        case Kind::Leq: tightenHi(c); break;
        case Kind::Gt:  tightenLo(c + 1); break;
        case Kind::Lt:  tightenHi(c - 1); break;
        case Kind::Eq:  tightenLo(c); tightenHi(c); break;
        default: return false;
    }
    return true;
}

void ModularConsistencyChecker::crtCombine(
    const mpz_class& a1, const mpz_class& n1,
    const mpz_class& a2, const mpz_class& n2,
    mpz_class& a, mpz_class& n, bool& ok) {

    // Extended gcd: g = s*n1 + t*n2.
    mpz_class g, s, t;
    mpz_gcdext(g.get_mpz_t(), s.get_mpz_t(), t.get_mpz_t(),
               n1.get_mpz_t(), n2.get_mpz_t());

    mpz_class diff = a2 - a1;
    if (mpz_divisible_p(diff.get_mpz_t(), g.get_mpz_t()) == 0) {
        ok = false;
        return;
    }

    mpz_class lcm = (n1 / g) * n2;            // = lcm(n1, n2)
    mpz_class step = n1 * s * (diff / g);     // a1 + step ≡ a2 (mod n2)
    mpz_class cand = a1 + step;

    // Normalize into [0, lcm).
    mpz_class r = cand % lcm;
    if (r < 0) r += lcm;

    a  = r;
    n  = lcm;
    ok = true;
}

ExprId ModularConsistencyChecker::mkFalse() {
    CoreExpr e;
    e.kind    = Kind::ConstBool;
    e.sort    = boolSortId_;
    e.payload = Payload(false);
    return ir_.add(std::move(e));
}

ExprId ModularConsistencyChecker::mkIntConst(const mpz_class& v) {
    CoreExpr e;
    e.kind    = Kind::ConstInt;
    e.sort    = intSortId_;
    e.payload = Payload(static_cast<int64_t>(v.get_si()));
    return ir_.add(std::move(e));
}

ExprId ModularConsistencyChecker::mkEq(ExprId a, ExprId b) {
    CoreExpr e;
    e.kind = Kind::Eq;
    e.sort = boolSortId_;
    e.children.push_back(a);
    e.children.push_back(b);
    return ir_.add(std::move(e));
}

void ModularConsistencyChecker::run() {
    std::unordered_map<ExprId, std::vector<ModConstraint>> modByVar;
    std::unordered_map<ExprId, VarBounds> bounds;

    auto scoped = ir_.getScopedAssertions();
    for (const auto& [level, assertion] : scoped) {
        if (auto mc = matchModEq(assertion, level)) {
            modByVar[mc->varExpr].push_back(*mc);
            continue;
        }
        matchBound(assertion, level, bounds);
    }

    for (const auto& kv : modByVar) {
        ExprId varExpr = kv.first;
        const auto& mods = kv.second;
        if (mods.empty()) continue;

        // CRT-aggregate.
        auto normResidue = [](const mpz_class& a, const mpz_class& n) {
            mpz_class r = a % n;
            if (r < 0) r += n;
            return r;
        };

        mpz_class agg_a = normResidue(mods[0].residue, mods[0].modulus);
        mpz_class agg_n = mods[0].modulus;
        bool inconsistent = false;
        for (size_t i = 1; i < mods.size(); ++i) {
            mpz_class ai = normResidue(mods[i].residue, mods[i].modulus);
            mpz_class a, n;
            bool ok = false;
            crtCombine(agg_a, agg_n, ai, mods[i].modulus, a, n, ok);
            if (!ok) {
                inconsistent = true;
                break;
            }
            agg_a = a;
            agg_n = n;
        }

        ScopeLevel level = mods.back().level;

        if (inconsistent) {
            ir_.addAssertion(mkFalse(), level);
            continue;
        }

        auto bIt = bounds.find(varExpr);
        if (bIt == bounds.end() || !bIt->second.lo || !bIt->second.hi) continue;

        const mpz_class& lo = *bIt->second.lo;
        const mpz_class& hi = *bIt->second.hi;
        if (lo > hi) continue;

        mpz_class k = (agg_a - lo) % agg_n;
        if (k < 0) k += agg_n;
        mpz_class start = lo + k;

        if (start > hi) {
            ir_.addAssertion(mkFalse(), level);
            continue;
        }

        // Single candidate in range — pin x. Otherwise leave as-is.
        if (start + agg_n > hi) {
            ir_.addAssertion(mkEq(varExpr, mkIntConst(start)), level);
        }
    }
}

} // namespace zolver
