#pragma once

#include "theory/arith/kernel/linearizer/LinearizationTypes.h"
#include <vector>
#include <optional>

namespace xolver {

// PowerCutGenerator emits convex-envelope linear cuts for the auxiliary
// variable `s` that represents x^N (with N >= 3, fixed integer).
//
// Soundness model
//   Each cut is a globally-valid linear relaxation of the polynomial
//   identity s = x^N. The cuts together form a polyhedron that contains
//   the graph of s = x^N restricted to the box [l, u]. Specifically:
//
//   Tangent (always lower bound): s >= a^N + N*a^(N-1)*(x - a)
//     Justification: x^N is convex on x >= 0 for all N >= 2, and on
//     x <= 0 when N is even. Tangent at point a lies below the curve.
//     The cut is sound on the entire real line whenever the convexity
//     holds at every point along the active interval.
//
//   Secant (upper bound on a convex piece): s <= ((u^N - l^N)/(u - l))*x
//                                              + (l^N - ((u^N - l^N)/(u - l))*l)
//     Justification: convex chord lies above the curve. Requires N even
//     OR the sign-known interval [l, u] (both endpoints same sign).
//
//   Nonneg (only for N even or strict-positive x): s >= 0.
//
//   Sign envelope (odd N, no finite upper bound): s has the same sign
//     as x (since x^N for odd N preserves sign).
//
// Tangent-point selection: caller passes a candidate `modelX` (the
// current LRA-sibling assignment for x). If null, falls back to the
// bound midpoint, which is the safest model-free choice.
//
// Bernstein hook (DESIGN): the Bernstein expansion of x^N on [l, u]
// provides a TIGHTER piecewise-linear envelope than tangent + secant
// alone (cvc5 uses tangent + secant). Future Phase 1b will introduce
// a BernsteinPowerCutGenerator that emits ALL Bernstein control points
// as additional cuts; the same cut-driver API (emit + cache + lemma)
// applies, so it slots in alongside PowerCutGenerator without changing
// the IncrementalLinearizer plumbing.
class PowerCutGenerator {
public:
    // exponent must be >= 3 (N=2 is handled by SquareCutGenerator).
    std::vector<LinearCut> generate(
        const AuxTerm& s,
        const std::string& x,
        int exponent,
        const BoundInfo& xBounds,
        SatLit nonlinearReason,
        const std::optional<mpq_class>& modelX,
        bool emitNonneg = true,
        bool emitSecant = true,
        bool emitTangent = true,
        SortKind sort = SortKind::Real);

private:
    // mpq^N for non-negative N. Used for closed-form tangent and secant.
    static mpq_class powQ(const mpq_class& base, int exponent);
};

} // namespace xolver
