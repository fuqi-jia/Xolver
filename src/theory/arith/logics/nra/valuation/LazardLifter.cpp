#include "theory/arith/logics/nra/valuation/LazardLifter.h"
#include "theory/arith/logics/nra/valuation/TowerRootIsolation.h"   // isolateRealRootsInTower

namespace xolver {

// Increment 1 — sound but conservative. The exact oracle's gcd-based Keep test
// assumes its defPoly is the candidate's MINIMAL rational poly (Q-irreducible).
// Combining several polys' Norms into one defining poly violates that (the gcd
// becomes a proper factor reducible already over Q, which the oracle treats as
// Unknown). So we lift PER polynomial — each over its own Norm — and only place
// roots when exactly ONE polynomial contributes real-root boundaries at this
// level. A genuine cross-polynomial merge needs Q-factorization (or Trager) to
// give each candidate its minimal defining poly; until then a multi-contributor
// lift returns unsupported (=> caller falls back to Collins, never UNSAT).
LazardLiftResult lazardLift(const std::vector<RationalPolynomial>& polys,
                            VarId mainVar, const TowerContext& ctx) {
    LazardLiftResult out;

    int contributors = 0;
    for (const auto& F : polys) {
        if (!F.contains(mainVar)) continue;            // constant in mainVar: no boundary
        auto r = isolateRealRootsInTower(F, mainVar, ctx);
        if (!r.supported) return LazardLiftResult{};   // any inconclusive poly => unsupported
        if (r.rootIntervals.empty()) continue;         // this poly has no real roots here
        if (++contributors >= 2)                       // multi-contributor merge deferred
            return LazardLiftResult{};
        out.defPoly = r.norm;
        out.sections.clear();
        for (const auto& iv : r.rootIntervals)
            out.sections.push_back({iv.first, iv.second});
    }

    // contributors == 0: no boundaries => a single (-inf,+inf) sector (supported,
    // empty sections). contributors == 1: the sole poly's kept roots (already
    // ascending, disjoint over out.defPoly).
    out.supported = true;
    return out;
}

}  // namespace xolver
