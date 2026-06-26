#include "theory/arith/kernel/linearizer/BernsteinPowerCutGenerator.h"
#include <algorithm>

namespace xolver {

mpq_class BernsteinPowerCutGenerator::powQ(const mpq_class& base, int exp) {
    mpq_class r = 1;
    for (int i = 0; i < exp; ++i) r *= base;
    return r;
}

mpq_class BernsteinPowerCutGenerator::binom(int n, int k) {
    if (k < 0 || k > n) return mpq_class(0);
    if (k == 0 || k == n) return mpq_class(1);
    mpq_class r = 1;
    for (int i = 1; i <= k; ++i) {
        r *= mpq_class(n - i + 1);
        r /= mpq_class(i);
    }
    return r;
}

// Bernstein coefficients of x^N on [l, u]
//
//   x = (1-t)·l + t·u  with t in [0, 1]
//   x^N = ((1-t)·l + t·u)^N = Σ_{j=0..N} C(N, j) · l^{N-j} · t^j · (u-l)^j
//
// Bernstein representation of t^j in degree N:
//   t^j = Σ_{i=j..N} (C(i, j) / C(N, j)) · B_{i, N}(t)
//
// Substitute:
//   x^N = Σ_{j=0..N} C(N, j) · l^{N-j} · (u-l)^j · t^j
//       = Σ_{i=0..N} (Σ_{j=0..i} C(i, j) · l^{N-j} · (u-l)^j) · B_{i, N}(t)
//
// So  b_i = Σ_{j=0..i} C(i, j) · l^{N-j} · (u-l)^j .
//
// Sanity: b_0 = l^N. b_N = Σ_{j=0..N} C(N, j) · l^{N-j} · (u-l)^j = u^N.  ✓
std::vector<mpq_class> BernsteinPowerCutGenerator::bernsteinCoeffs(
    int N, const mpq_class& l, const mpq_class& u) {

    std::vector<mpq_class> b(N + 1, mpq_class(0));
    mpq_class du = u - l;
    // Cache l^{N-j}  for j = 0..N
    std::vector<mpq_class> lPow(N + 1);
    lPow[0] = powQ(l, N);
    if (l != 0) {
        for (int j = 1; j <= N; ++j) lPow[j] = lPow[j - 1] / l;
    } else {
        // l == 0: l^{N-j} is 0 for j < N and 1 for j == N.
        for (int j = 1; j <= N; ++j) lPow[j] = mpq_class(0);
        lPow[N] = mpq_class(1);
    }
    // Cache (u-l)^j for j = 0..N
    std::vector<mpq_class> duPow(N + 1);
    duPow[0] = mpq_class(1);
    for (int j = 1; j <= N; ++j) duPow[j] = duPow[j - 1] * du;

    for (int i = 0; i <= N; ++i) {
        mpq_class s = 0;
        for (int j = 0; j <= i; ++j) {
            s += binom(i, j) * lPow[j] * duPow[j];
        }
        b[i] = s;
    }
    return b;
}

std::vector<LinearCut> BernsteinPowerCutGenerator::generate(
    const AuxTerm& s,
    const std::string& x,
    int exponent,
    const BoundInfo& xBounds,
    SatLit nonlinearReason,
    const Options& opt,
    SortKind sort) {

    std::vector<LinearCut> cuts;
    if (exponent < 2) return cuts;
    if (!xBounds.hasFiniteCompleteBounds()) return cuts;
    if (xBounds.lower == xBounds.upper) return cuts;

    const mpq_class& l = xBounds.lower;
    const mpq_class& u = xBounds.upper;

    auto coeffs = bernsteinCoeffs(exponent, l, u);
    // Convex-hull envelope: x^N is bounded above by max(b_i) and below by
    // min(b_i) on the entire box. These are global linear cuts independent
    // of x — emitted as constant bounds on s.
    mpq_class bMin = coeffs[0];
    mpq_class bMax = coeffs[0];
    for (const auto& c : coeffs) {
        if (c < bMin) bMin = c;
        if (c > bMax) bMax = c;
    }

    std::vector<SatLit> reasons{nonlinearReason};
    reasons.insert(reasons.end(),
                   xBounds.lowerReasons.begin(), xBounds.lowerReasons.end());
    reasons.insert(reasons.end(),
                   xBounds.upperReasons.begin(), xBounds.upperReasons.end());

    // We compare against the trivial endpoint-only bound  [min(l^N,u^N),
    // max(l^N,u^N)]  to decide whether the Bernstein envelope is genuinely
    // tighter than what a one-shot interval evaluation already supplies. For
    // convex pieces (l>=0 OR N even with sign-determinate interval), the
    // Bernstein max == endpoint max, so the upper cut is trivial; skip it
    // when opt.skipTrivial.
    mpq_class lN = powQ(l, exponent);
    mpq_class uN = powQ(u, exponent);
    mpq_class trivialMin = std::min(lN, uN);
    mpq_class trivialMax = std::max(lN, uN);
    // For mixed-sign even-N, trivial min should be 0:
    if ((exponent % 2) == 0 && l <= 0 && u >= 0) trivialMin = mpq_class(0);

    bool emitLow = !opt.skipTrivial || bMin > trivialMin;
    bool emitHigh = !opt.skipTrivial || bMax < trivialMax;

    if (emitLow && cuts.size() < opt.maxCutsHere) {
        ZeroLinearConstraint z;
        z.expr.terms.push_back({s.name, mpq_class(-1)});
        z.expr.constant = bMin;
        z.rel = Relation::Leq;
        z.sort = sort;
        z.debugTag = "bernstein_hull_lower";
        cuts.push_back({std::move(z), reasons, "bernstein_hull_lower"});
    }
    if (emitHigh && cuts.size() < opt.maxCutsHere) {
        ZeroLinearConstraint z;
        z.expr.terms.push_back({s.name, mpq_class(1)});
        z.expr.constant = -bMax;
        z.rel = Relation::Leq;
        z.sort = sort;
        z.debugTag = "bernstein_hull_upper";
        cuts.push_back({std::move(z), reasons, "bernstein_hull_upper"});
    }

    // Piecewise linear support cuts: the lower envelope of the Bernstein
    // control polygon (i, b_i) — when viewed as control points spanning the
    // x-coordinate range [l, u] uniformly at i*du/N — supplies sound linear
    // lower-bound supports for x^N when the underlying function is convex
    // on its segment. We emit at most opt.maxCutsHere - cuts.size() of
    // these, one per adjacent pair of control points.
    //
    // Control point x-coord: x_i = l + i * (u - l) / N. Slope between i, i+1
    // is  (b_{i+1} - b_i) / (du / N) = N * (b_{i+1} - b_i) / (u - l).
    // The line through (x_i, b_i) and (x_{i+1}, b_{i+1}) is
    //   line(x) = b_i + slope * (x - x_i)
    //
    // For convex x^N (even N, or odd N with l >= 0), the function lies
    // ABOVE every chord between control points except the secant — that's
    // not what we want. The CORRECT support cut is the tangent at the
    // control point's image (b_i, x_i), but b_i is in general NOT on the
    // curve x^N except at i=0 and i=N. So control-polygon chords don't
    // automatically give support cuts.
    //
    // What DOES hold is: the LOWER envelope of the control polygon is a
    // sound lower bound for x^N on convex pieces, and the UPPER envelope
    // is a sound upper bound on concave pieces (by Bernstein-Bezier convex
    // hull). The global max/min cuts above are already the tightest
    // information at the convex-hull level. Per-segment piecewise cuts
    // would require de Casteljau subdivision (degree elevation) which is
    // not warranted at this generator's complexity budget — that's a
    // dedicated Phase 1c follow-up.

    return cuts;
}

} // namespace xolver
