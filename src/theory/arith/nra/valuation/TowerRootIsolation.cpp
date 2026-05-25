#include "theory/arith/nra/valuation/TowerRootIsolation.h"
#include "theory/arith/nra/projection/SubresultantChain.h"

namespace nlcolver {

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
    // B.2.b (exact filter) not yet implemented: the Norm alone is a superset and
    // its extraneous roots would create unsound section cells. Report
    // unsupported so the caller degrades to Unknown (never UNSAT).
    (void)F; (void)mainVar; (void)ctx;
    return TowerRootResult{};   // supported = false
}

}  // namespace nlcolver
