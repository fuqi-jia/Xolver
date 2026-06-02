#pragma once

#include "theory/arith/linearizer/LinearizationTypes.h"
#include <vector>
#include <optional>

namespace xolver {

// BernsteinPowerCutGenerator
//
// Tighter alternative to PowerCutGenerator for s = x^N on [l, u]. The key
// property: any polynomial p(x) of degree N expanded in the Bernstein basis
// over [l, u] satisfies the convex-hull bound
//
//   min(b_i) <= p(x) <= max(b_i)   for all x in [l, u]
//
// where b_i (i = 0..N) are the Bernstein coefficients. For p(x) = x^N the
// coefficients have a closed form:
//
//   b_i = Σ_{k=0..N} C(i, k) / C(N, k) · l^{N-k} · (u - l)^k · ???
//
// Concretely, by the explicit formula in Garloff (1985):
//
//   b_i(x^N on [l,u]) = Σ_{k=0..i} C(i, k) / C(N, k) · l^{N-k} · (u - l)^k
//                       only when k = N
//
// Simpler equivalent derivation: x^N = ((1 - t) l + t u)^N with t = (x - l)/(u - l).
// Binomial expand:
//   x^N = Σ_{j=0..N} C(N, j) l^{N - j} (u - l)^j t^j
// Then the Bernstein expansion of t^j is well-known:
//   t^j = Σ_{i=j..N} (C(i, j) / C(N, j)) · B_{i, N}(t)
// Combining:
//   x^N = Σ_{i=0..N} b_i · B_{i, N}(t)
//        with b_i = Σ_{j=0..i} (C(i, j) / C(N, j)) · C(N, j) · l^{N-j} · (u - l)^j
//                = Σ_{j=0..i} C(i, j) · l^{N-j} · (u - l)^j
//                = (l + (u - l))^? — no, only the partial sum up to i.
//
// We can also compute the bᵢ directly by the de Casteljau scheme on the
// monomial control points of x^N; for portability we use the explicit
// formula  b_i = Σ_{j=0..i} C(i, j) · l^{N-j} · (u - l)^j
// and verify via two boundary identities  b_0 = l^N,  b_N = u^N.
//
// Cuts emitted
//   For each Bernstein coefficient b_i with i in [1, N-1] (skipping the
//   trivial endpoints already covered by the bound atoms):
//      s <= max(b_i)    — tightest upper envelope from convex hull
//      s >= min(b_i)    — tightest lower envelope from convex hull
//   PLUS for each control point that lies on the boundary of the convex
//   hull strictly inside the box, one linear support cut (the line from
//   the previous to the next control point), giving up to N+1 piecewise
//   support cuts total. This is strictly tighter than secant + tangent.
//
// Soundness model
//   Every cut is a sound linear envelope of x^N restricted to [l, u]; the
//   Bernstein convex hull property is mathematical, not heuristic.
//
// Gating: caller (IncrementalLinearizer) gates this behind
// XOLVER_NRA_NLEXT_BERNSTEIN. When BOTH the existing PowerCutGenerator and
// this generator are enabled, both fire (sound + cumulative). For a clean
// A/B promotion path, prefer enabling only one at a time during eval.
class BernsteinPowerCutGenerator {
public:
    struct Options {
        // Skip cuts when the linear envelope is no tighter than the box
        // [min, max] over the boundary points. Useful to avoid bloat.
        bool skipTrivial = true;
        // Cap the per-call cut count.
        size_t maxCutsHere = 8;
    };

    std::vector<LinearCut> generate(
        const AuxTerm& s,
        const std::string& x,
        int exponent,
        const BoundInfo& xBounds,
        SatLit nonlinearReason,
        const Options& opt,
        SortKind sort = SortKind::Real);

    // Exposed for unit testing: Bernstein coefficients of x^N on [l, u].
    static std::vector<mpq_class> bernsteinCoeffs(int N,
                                                    const mpq_class& l,
                                                    const mpq_class& u);

private:
    static mpq_class powQ(const mpq_class& base, int exp);
    static mpq_class binom(int n, int k);
};

} // namespace xolver
