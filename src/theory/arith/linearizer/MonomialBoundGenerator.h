#pragma once

#include "theory/arith/linearizer/LinearizationTypes.h"
#include <vector>
#include <optional>
#include <string>

namespace xolver {

class PolynomialKernel;

// MonomialBoundGenerator — Phase 2 of the incremental-linearization upgrade.
//
// Produces linear cuts that bound a compound monomial aux variable
//
//   s = c · x_1^{e_1} · x_2^{e_2} · ... · x_k^{e_k}
//
// (with k >= 2 factors after Power/Square/Product have already been peeled
// off — those have dedicated, tighter generators).
//
// Why this generator exists
//   The legacy HigherMixed path in IncrementalLinearizer only emits a *sign*
//   lemma (sign(s) is determinate when each factor's sign is). That is enough
//   for sign-based UNSAT but useless when the formula needs an actual
//   numeric bound: `lambda1 * vv1 * vv3^8 >= 1 /\ |lambda1| < 1 /\ |vv1| < 1
//   /\ |vv3| < 1` should imply `s < 1`, which the sign lemma cannot express.
//
// Cuts produced (each globally sound, each strictly stronger than the next
// when bounds are tight)
//
//   1. Interval envelope (always emitted when every factor has finite
//      complete bounds on each side it matters)
//          s_lo <= s <= s_hi
//      where the corners are chosen by sign-arithmetic on the per-factor
//      interval value ranges. Even-exponent factor x_i^{e_i} ranges over
//      [0, max(l_i^e_i, u_i^e_i)] when 0 in [l_i, u_i], otherwise over the
//      tight [min, max] of the endpoint powers. Odd-exponent factor ranges
//      monotonically with x_i. The total monomial range is the product of
//      these per-factor ranges scaled by c.
//
//   2. Pivot-corner cuts (k cuts when bounds known)
//      For each factor x_k as the pivot, define the "rest product"
//          R = c · ∏_{i != k} x_i^{e_i}
//      and bound R by an interval [R_lo, R_hi] via step 1 over the
//      *remaining* factors. Then on the slice where x_k^{e_k} ranges over
//      [P_lo, P_hi], the bilinear identity s = R · x_k^{e_k} admits
//      McCormick-style envelopes
//          s >= R_lo * x_k^{e_k} + R * P_lo - R_lo * P_lo   (when R >= R_lo)
//          s <= R_hi * x_k^{e_k} + R * P_lo - R_hi * P_lo   (when R <= R_hi)
//      but x_k^{e_k} itself is *not* linear when e_k > 1, so we collapse to
//      the linear-in-x_k forms by using the per-pivot endpoint values of
//      x_k^{e_k} at x_k = l_k and x_k = u_k. That gives a sound linear
//      relaxation: for a monotone branch on x_k,
//          slope_pos = (R_hi * u_k^{e_k} - R_lo * l_k^{e_k}) / (u_k - l_k)
//          s <= slope_pos * (x_k - l_k) + R_lo * l_k^{e_k}     (upper)
//          s >= slope_neg * (x_k - l_k) + R_hi * l_k^{e_k}     (lower)
//      Direction is chosen by sign of the rest-product to keep the cut
//      sound regardless of x_k's branch.
//
//   3. Linear-in-pivot tangent at the model point (when model values
//      available for every factor)
//      Multi-variable first-order Taylor of f(x_1, ..., x_k) = c·∏ x_i^{e_i}
//      around the model point m = (m_1, ..., m_k):
//          f(x) ~ f(m) + Σ_i (∂f/∂x_i)(m) · (x_i - m_i)
//      For x_i^{e_i} convex in x_i on the active sign branch, that tangent
//      hyperplane lies *below* f, so it is a sound LOWER bound on s. We
//      restrict to the all-nonneg case (every factor has a known
//      nonneg-or-strict-pos lower bound and every exponent is positive) to
//      avoid sign-branch case analysis in this Phase 2 cut; the harder
//      mixed-sign case is gated to later phases.
//
// Soundness contract (same as PowerCutGenerator / SquareCutGenerator)
//   - Each emitted ZeroLinearConstraint is sound *for all* x in the box
//     described by the bound reasons attached to the cut.
//   - The cut's reason list includes the nonlinear-clause activation literal
//     plus the bound atoms used to derive the corners.
//   - Cuts beyond the SAT layer's capacity are dropped silently (cache /
//     maxCutsPerTerm), never falsified.
//
// Gating: caller (IncrementalLinearizer) gates the entire generator behind
// XOLVER_NRA_NLEXT_MONO_BOUND so this can ride alongside the existing
// XOLVER_NRA_NLEXT_HIGHER sign-lemma path during validation.
class MonomialBoundGenerator {
public:
    struct Factor {
        std::string var;
        int exponent;
        BoundInfo bounds;                  // copy; reasons must accompany
        std::optional<mpq_class> modelVal; // current LRA-sibling value, if any
    };

    struct Options {
        bool emitSignOnly     = true;  // cut family 0 (NEW: sign-only, no upper bound)
        bool emitInterval     = true;  // cut family 1
        bool emitPivotCorner  = true;  // cut family 2
        bool emitTangentPlane = true;  // cut family 3
        // Cap on per-call cuts to avoid lemma flooding for k-large monomials.
        // The IncrementalLinearizer further caps via config.maxCutsPerTerm.
        size_t maxCutsHere = 16;
    };

    // No default for `opt` to dodge the C++ "default member initializer in
    // enclosing-class context" restriction. Caller constructs Options{}.
    std::vector<LinearCut> generate(
        const AuxTerm& s,
        const mpq_class& coefficient,        // the c in c·∏ x_i^{e_i}
        const std::vector<Factor>& factors,  // already sorted by var name
        SatLit nonlinearReason,
        const Options& opt,
        SortKind sort = SortKind::Real);

private:
    // Per-factor value range x^e on the bound box. Returns nullopt if
    // either bound is missing or the range cannot be made finite (e.g.
    // odd-exponent factor with no finite bounds, even-exponent factor with
    // mixed-sign interval requires only [0, max(l^e, u^e)]).
    static std::optional<std::pair<mpq_class, mpq_class>> factorRange(
        const Factor& f);

    // Compute the product range [lo, hi] of an arbitrary collection of
    // per-factor ranges scaled by the coefficient. Returns nullopt if any
    // factor's range is missing.
    static std::optional<std::pair<mpq_class, mpq_class>> productRange(
        const mpq_class& coefficient,
        const std::vector<std::optional<std::pair<mpq_class, mpq_class>>>&
            perFactor);

    // mpq^N. Helper.
    static mpq_class powQ(const mpq_class& base, int exponent);
};

} // namespace xolver
