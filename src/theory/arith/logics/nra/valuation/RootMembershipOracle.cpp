#include "theory/arith/logics/nra/valuation/RootMembershipOracle.h"
#include "theory/arith/logics/nra/valuation/TowerPolyGcd.h"
#include "theory/arith/logics/nra/valuation/RationalRootIsolation.h"
#include "theory/arith/logics/nra/projection/Squarefree.h"
#include <algorithm>
#include <map>

namespace xolver {

namespace {

struct Ival { mpq_class lo, hi; };
Ival iConst(const mpq_class& c) { return {c, c}; }
Ival iAdd(const Ival& a, const Ival& b) { return {a.lo + b.lo, a.hi + b.hi}; }
Ival iMul(const Ival& a, const Ival& b) {
    mpq_class p1 = a.lo * b.lo, p2 = a.lo * b.hi, p3 = a.hi * b.lo, p4 = a.hi * b.hi;
    return {std::min({p1, p2, p3, p4}), std::max({p1, p2, p3, p4})};
}
Ival iPow(const Ival& a, int n) { Ival r = iConst(mpq_class(1)); for (int i = 0; i < n; ++i) r = iMul(r, a); return r; }
int iSign(const Ival& a) { if (a.lo > 0) return 1; if (a.hi < 0) return -1; return 0; }
bool iExcludesZero(const Ival& a) { return a.lo > 0 || a.hi < 0; }

bool evalInterval(const RationalPolynomial& p, const std::map<VarId, Ival>& asg, Ival& out) {
    out = iConst(mpq_class(0));
    for (const auto& [mon, coeff] : p.terms()) {
        Ival term = iConst(coeff);
        for (const auto& [v, e] : mon) {
            auto it = asg.find(v);
            if (it == asg.end()) return false;
            term = iMul(term, iPow(it->second, e));
        }
        out = iAdd(out, term);
    }
    return true;
}
Ival refineVar(VarId v, Ival iv, const RationalPolynomial& defPoly,
               const std::map<VarId, Ival>& otherAsg, int iters) {
    for (int t = 0; t < iters; ++t) {
        if (iv.lo == iv.hi) break;
        mpq_class mid = (iv.lo + iv.hi) / 2;
        std::map<VarId, Ival> a = otherAsg;
        a[v] = iConst(iv.lo); Ival flo; if (!evalInterval(defPoly, a, flo)) break;
        a[v] = iConst(mid);   Ival fmid; if (!evalInterval(defPoly, a, fmid)) break;
        int slo = iSign(flo), smid = iSign(fmid);
        if (slo == 0 || smid == 0) break;
        if (slo != smid) iv.hi = mid; else iv.lo = mid;
    }
    return iv;
}

// Build the generator box [lower,upper] per generator; false if intervals absent.
bool genBox(const TowerContext& ctx, std::vector<Ival>& out) {
    if (ctx.generators.size() != ctx.extensionVars.size()) return false;
    out.clear();
    for (const auto& g : ctx.generators) {
        if (g.isRational()) out.push_back(iConst(g.rational));
        else out.push_back({g.root.lower, g.root.upper});
    }
    return true;
}

}  // namespace

RootMembership lazardRootMembership(const RationalPolynomial& F, VarId targetVar,
                                    const RationalPolynomial& defPoly,
                                    const mpq_class& betaLo, const mpq_class& betaHi,
                                    const TowerContext& ctx) {
    TowerKernel K(ctx);

    std::vector<Ival> genBase;
    bool haveBox = genBox(ctx, genBase);

    // (0) Rational beta: exact substitution + tower zero-test.
    //   v == 0 in the ring  => F(beta) is in the ideal <m_0,..> => F(beta)=0 at the
    //     real embedding (a genuine common root of the m_i): KEEP, sound for ANY
    //     monic tower (even a reducible one).
    //   v != 0 in the ring  does NOT prove F(beta)!=0 when the tower is reducible
    //     (a ring-nonzero element can still vanish at the chosen real branch). So
    //     witness nonzero by a real interval enclosure over the generator box;
    //     inconclusive => Unknown (never a bare ring-nonzero DROP).
    if (betaLo == betaHi) {
        RationalPolynomial sub = F.substituteRational(targetVar, betaLo);
        TowerElement v = K.reduce(sub);
        if (v.isZero()) return RootMembership::Keep;
        if (haveBox) {
            std::vector<Ival> gen = genBase;
            for (int iter = 0; iter < 48; ++iter) {
                std::map<VarId, Ival> asg;
                for (size_t i = 0; i < ctx.extensionVars.size(); ++i) asg[ctx.extensionVars[i]] = gen[i];
                Ival rv;
                if (!evalInterval(v.value, asg, rv)) break;
                if (iExcludesZero(rv)) return RootMembership::Drop;
                for (size_t i = 0; i < ctx.extensionVars.size(); ++i) {
                    std::map<VarId, Ival> lower;
                    for (size_t j = 0; j < i; ++j) lower[ctx.extensionVars[j]] = gen[j];
                    gen[i] = refineVar(ctx.extensionVars[i], gen[i], ctx.minimalPolys[i], lower, 1);
                }
            }
        }
        return RootMembership::Unknown;
    }

    auto sf = squarefreePartWrt(defPoly, targetVar);
    if (!sf.complete) return RootMembership::Unknown;
    const RationalPolynomial& Nsf = sf.poly;

    // (1) Interval fast-DROP: F(alpha, beta) provably != 0.
    if (haveBox) {
        Ival beta{betaLo, betaHi};
        std::vector<Ival> gen = genBase;
        for (int iter = 0; iter < 48; ++iter) {
            std::map<VarId, Ival> asg;
            asg[targetVar] = beta;
            for (size_t i = 0; i < ctx.extensionVars.size(); ++i) asg[ctx.extensionVars[i]] = gen[i];
            Ival fv;
            if (!evalInterval(F, asg, fv)) break;
            if (iExcludesZero(fv)) return RootMembership::Drop;
            beta = refineVar(targetVar, beta, Nsf, {}, 1);
            for (size_t i = 0; i < ctx.extensionVars.size(); ++i) {
                std::map<VarId, Ival> lower;
                for (size_t j = 0; j < i; ++j) lower[ctx.extensionVars[j]] = gen[j];
                gen[i] = refineVar(ctx.extensionVars[i], gen[i], ctx.minimalPolys[i], lower, 1);
            }
        }
    }

    // (2) Exact via gcd over K of F and the squarefree defPoly.
    auto G = towerPolyGcd(F, Nsf, targetVar, K);
    if (!G.ok) return RootMembership::Unknown;
    int dg = G.gcd.degree(targetVar);
    int dq = Nsf.degree(targetVar);
    if (dg <= 0) return RootMembership::Drop;     // coprime: beta not a root of F
    if (dg == dq) return RootMembership::Keep;    // sf | F: every root of sf (incl beta) is a root of F

    // (3) G is a proper factor. If linear, its root is a tower element c (a root
    // of sf); decide beta == c exactly via interval refinement + Sturm count.
    if (dg == 1 && haveBox) {
        auto coeffs = G.gcd.coefficients(targetVar);   // [c0, c1]
        if (coeffs.size() < 2) return RootMembership::Unknown;
        TowerElement c1 = K.reduce(coeffs[1]);
        TowerElement c0 = K.reduce(coeffs[0]);
        auto cElem = K.div(K.neg(c0), c1);              // root c = -c0/c1
        if (!cElem) return RootMembership::Unknown;
        const RationalPolynomial& cVal = cElem->value;  // tower element (in ext vars)

        Ival beta{betaLo, betaHi};
        std::vector<Ival> gen = genBase;
        for (int iter = 0; iter < 80; ++iter) {
            // c's real interval over the (refined) generator box
            std::map<VarId, Ival> casg;
            for (size_t i = 0; i < ctx.extensionVars.size(); ++i) casg[ctx.extensionVars[i]] = gen[i];
            Ival cIval;
            if (!evalInterval(cVal, casg, cIval)) return RootMembership::Unknown;
            // disjoint => beta != c
            if (cIval.hi < beta.lo || beta.hi < cIval.lo) return RootMembership::Drop;
            // both are roots of sf; if the merged span holds exactly one root of
            // sf, c and beta are that same root => Keep.
            mpq_class mlo = std::min(cIval.lo, beta.lo), mhi = std::max(cIval.hi, beta.hi);
            int cnt = countRealRootsIn(Nsf, targetVar, mlo, mhi);
            if (cnt == 1) return RootMembership::Keep;
            // refine and retry
            beta = refineVar(targetVar, beta, Nsf, {}, 1);
            for (size_t i = 0; i < ctx.extensionVars.size(); ++i) {
                std::map<VarId, Ival> lower;
                for (size_t j = 0; j < i; ++j) lower[ctx.extensionVars[j]] = gen[j];
                gen[i] = refineVar(ctx.extensionVars[i], gen[i], ctx.minimalPolys[i], lower, 1);
            }
        }
    }

    return RootMembership::Unknown;   // higher-degree proper factor: needs Trager
}

}  // namespace xolver
