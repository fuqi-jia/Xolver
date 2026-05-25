#include "theory/arith/nra/valuation/TowerRootIsolation.h"
#include "theory/arith/nra/valuation/RationalRootIsolation.h"
#include "theory/arith/nra/projection/SubresultantChain.h"
#include "theory/arith/nra/projection/Squarefree.h"
#include <algorithm>
#include <map>

namespace nlcolver {

namespace {

// Rational interval arithmetic for the [H2] fast filter (sound over-approx).
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

// Evaluate p over a box assignment (var -> Ival). false if a variable is unassigned.
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

// Bisect v's interval, keeping the root of defPoly inside, while the sign at the
// endpoints is determinate (otherAsg gives the other vars' intervals). Stops on
// an indeterminate step (sound: just a looser interval).
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

}  // namespace

TowerNormResult towerNorm(const RationalPolynomial& F, VarId mainVar,
                          const TowerContext& ctx, int maxMatrixDim) {
    TowerNormResult out;
    RationalPolynomial N = F;
    N.normalize();

    // Eliminate extension variables highest-first. N = Res_{A_i}(m_i, N).
    for (int i = static_cast<int>(ctx.extensionVars.size()) - 1; i >= 0; --i) {
        VarId Ai = ctx.extensionVars[i];
        if (!N.contains(Ai)) continue;            // F independent of this generator
        auto chain = principalSubresultantCoefficients(ctx.minimalPolys[i], N, Ai, maxMatrixDim);
        if (chain.budgetExceeded) { out.ok = false; return out; }
        if (chain.psc.empty()) { out.ok = false; return out; }   // degenerate (deg < 1)
        N = chain.psc[0];                          // psc_0 == Res_{A_i}(m_i, N) up to sign
        N.normalize();
    }

    // After eliminating all extension variables only mainVar (or a constant)
    // may remain; anything else is a degenerate elimination.
    for (VarId Ai : ctx.extensionVars) {
        if (N.contains(Ai)) { out.ok = false; return out; }
    }
    for (VarId v : N.variables()) {
        if (v != mainVar) { out.ok = false; return out; }
    }

    out.norm = std::move(N);
    out.ok = true;
    return out;
}

TowerRootResult isolateRealRootsInTower(const RationalPolynomial& F, VarId mainVar,
                                        const TowerContext& ctx) {
    TowerRootResult out;   // supported = false by default

    // (1) Candidate generation: Norm over Q, then exact real-root isolation.
    auto nr = towerNorm(F, mainVar, ctx);
    if (!nr.ok) return out;                              // budget/degenerate => Unknown
    auto cands = isolateRationalRoots(nr.norm, mainVar);
    if (!cands.ok) return out;
    if (cands.roots.empty()) { out.supported = true; return out; }   // Norm has no real root => F none

    auto nsf = squarefreePartWrt(nr.norm, mainVar);      // simple-root refinement of beta
    if (!nsf.complete) return out;
    const RationalPolynomial& Nsf = nsf.poly;

    // The real embedding box (one interval per generator).
    if (ctx.generators.size() != ctx.extensionVars.size()) return out;
    std::vector<Ival> baseGen;
    baseGen.reserve(ctx.generators.size());
    for (const auto& g : ctx.generators) {
        if (g.isRational()) baseGen.push_back(iConst(g.rational));
        else                baseGen.push_back({g.root.lower, g.root.upper});
    }

    // (2) Interval fast-filter: a candidate is DROPPED iff F(alpha, beta) is
    // provably != 0 (box interval excludes 0) — this removes conjugate/extraneous
    // Norm roots. A candidate that cannot be excluded within the budget is a
    // potential real root: step 3 does not place it, so the whole isolation is
    // reported unsupported (=> caller Unknown). Only when EVERY candidate is
    // dropped do we conclude F has no real roots at this embedding.
    const int kBudget = 64;
    for (const auto& cand : cands.roots) {
        Ival beta{cand.lo, cand.hi};
        std::vector<Ival> gen = baseGen;
        bool dropped = false;
        for (int iter = 0; iter < kBudget; ++iter) {
            std::map<VarId, Ival> asg;
            asg[mainVar] = beta;
            for (size_t i = 0; i < ctx.extensionVars.size(); ++i)
                asg[ctx.extensionVars[i]] = gen[i];
            Ival fv;
            if (!evalInterval(F, asg, fv)) { dropped = false; break; }
            if (iExcludesZero(fv)) { dropped = true; break; }
            beta = refineVar(mainVar, beta, Nsf, {}, 1);
            for (size_t i = 0; i < ctx.extensionVars.size(); ++i) {
                std::map<VarId, Ival> lower;
                for (size_t j = 0; j < i; ++j) lower[ctx.extensionVars[j]] = gen[j];
                gen[i] = refineVar(ctx.extensionVars[i], gen[i], ctx.minimalPolys[i], lower, 1);
            }
        }
        if (!dropped) return out;   // potential real root => Unknown (exact keep is step 4)
    }
    out.supported = true;           // all candidates excluded => F has no real roots
    return out;
}

}  // namespace nlcolver
