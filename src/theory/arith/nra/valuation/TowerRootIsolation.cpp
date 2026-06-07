#include "theory/arith/nra/valuation/TowerRootIsolation.h"
#include "theory/arith/nra/valuation/RationalRootIsolation.h"
#include "theory/arith/nra/valuation/RootMembershipOracle.h"
#include "theory/arith/nra/projection/SubresultantChain.h"

namespace xolver {

TowerNormResult towerNorm(const RationalPolynomial& F, VarId mainVar,
                          const TowerContext& ctx, int maxMatrixDim,
                          PolynomialKernel* kernel) {
    TowerNormResult out;
    RationalPolynomial N = F;
    N.normalize();

    // Eliminate extension variables highest-first. N = Res_{A_i}(m_i, N).
    for (int i = static_cast<int>(ctx.extensionVars.size()) - 1; i >= 0; --i) {
        VarId Ai = ctx.extensionVars[i];
        if (!N.contains(Ai)) continue;            // F independent of this generator
        // With a kernel, force the libpoly PSC (no matrix-dim bound): the determinant
        // blows up on the high-degree nested resultants of ≥2-generator towers (the
        // Geogebra deep-tower TO). forcePsc = (kernel != nullptr); null => determinant.
        auto chain = principalSubresultantCoefficients(ctx.minimalPolys[i], N, Ai,
                                                       maxMatrixDim, kernel,
                                                       /*forcePsc=*/kernel != nullptr);
        if (chain.budgetExceeded) { out.ok = false; return out; }
        if (chain.psc.empty()) { out.ok = false; return out; }   // degenerate (deg < 1)
        N = chain.psc[0];                          // psc_0 == Res_{A_i}(m_i, N) up to sign
        N.normalize();
    }

    // After eliminating all extension variables only mainVar (or a constant)
    // may remain; anything else is a degenerate elimination.
    for (VarId Ai : ctx.extensionVars)
        if (N.contains(Ai)) { out.ok = false; return out; }
    for (VarId v : N.variables())
        if (v != mainVar) { out.ok = false; return out; }

    out.norm = std::move(N);
    out.ok = true;
    return out;
}

TowerRootResult isolateRealRootsInTower(const RationalPolynomial& F, VarId mainVar,
                                        const TowerContext& ctx) {
    TowerRootResult out;   // supported = false by default

    // (1) Norm over Q -> candidate real roots.
    auto nr = towerNorm(F, mainVar, ctx);
    if (!nr.ok) return out;                                // budget/degenerate => Unknown
    out.norm = nr.norm;
    auto cands = isolateRationalRoots(nr.norm, mainVar);
    if (!cands.ok) return out;
    if (cands.roots.empty()) { out.supported = true; return out; }   // no real roots at all

    // (2) Exact root-membership oracle places each candidate: Keep -> a real
    // root of F at the embedding; Drop -> conjugate/extraneous, discard; any
    // Unknown -> we cannot soundly place this level => report unsupported
    // (caller => Unknown). Unknown is NEVER treated as Drop.
    for (const auto& cand : cands.roots) {
        RootMembership m = lazardRootMembership(F, mainVar, nr.norm, cand.lo, cand.hi, ctx);
        if (m == RootMembership::Keep)      out.rootIntervals.push_back({cand.lo, cand.hi});
        else if (m == RootMembership::Drop) continue;
        else return TowerRootResult{};      // Unknown => unsupported
    }
    out.supported = true;
    return out;
}

}  // namespace xolver
