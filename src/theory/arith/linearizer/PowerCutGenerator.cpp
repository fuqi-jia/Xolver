#include "theory/arith/linearizer/PowerCutGenerator.h"

namespace xolver {

mpq_class PowerCutGenerator::powQ(const mpq_class& base, int exponent) {
    mpq_class r = 1;
    for (int i = 0; i < exponent; ++i) r *= base;
    return r;
}

std::vector<LinearCut> PowerCutGenerator::generate(
    const AuxTerm& s,
    const std::string& x,
    int exponent,
    const BoundInfo& xBounds,
    SatLit nonlinearReason,
    const std::optional<mpq_class>& modelX,
    bool emitNonneg,
    bool emitSecant,
    bool emitTangent,
    SortKind sort) {

    std::vector<LinearCut> cuts;
    if (exponent < 3) return cuts;   // square and below handled elsewhere

    const bool nIsEven = (exponent % 2) == 0;

    // ------------------------------------------------------------------
    // Cut 1: nonneg envelope.
    //   N even:   s >= 0  always  (x^N >= 0)
    //   N odd:    s >= 0  iff  x >= 0; requires sign-positive x.
    // ------------------------------------------------------------------
    if (emitNonneg) {
        bool emitGlobalNonneg = nIsEven ||
            (xBounds.hasLower && xBounds.lower >= 0);
        if (emitGlobalNonneg) {
            ZeroLinearConstraint z;
            z.expr.terms.push_back({s.name, mpq_class(-1)});
            z.rel = Relation::Leq;
            z.sort = sort;
            z.debugTag = "power_nonneg";
            std::vector<SatLit> reasons{nonlinearReason};
            if (!nIsEven) {
                // Reason needs the strict-positive lower bound on x.
                reasons.insert(reasons.end(),
                               xBounds.lowerReasons.begin(),
                               xBounds.lowerReasons.end());
            }
            cuts.push_back({std::move(z), std::move(reasons), "power_nonneg"});
        }
        // N odd + strict-negative x: s <= 0
        if (!nIsEven && xBounds.hasUpper && xBounds.upper <= 0) {
            ZeroLinearConstraint z;
            z.expr.terms.push_back({s.name, mpq_class(1)});
            z.rel = Relation::Leq;
            z.sort = sort;
            z.debugTag = "power_nonpos";
            std::vector<SatLit> reasons{nonlinearReason};
            reasons.insert(reasons.end(),
                           xBounds.upperReasons.begin(),
                           xBounds.upperReasons.end());
            cuts.push_back({std::move(z), std::move(reasons), "power_nonpos"});
        }
    }

    if (!xBounds.hasFiniteCompleteBounds()) {
        return cuts;
    }

    const mpq_class& l = xBounds.lower;
    const mpq_class& u = xBounds.upper;

    std::vector<SatLit> boundReasons = {nonlinearReason};
    boundReasons.insert(boundReasons.end(),
                        xBounds.lowerReasons.begin(), xBounds.lowerReasons.end());
    boundReasons.insert(boundReasons.end(),
                        xBounds.upperReasons.begin(), xBounds.upperReasons.end());

    // Convexity classification: x^N is convex on intervals where the second
    // derivative N*(N-1)*x^(N-2) is >= 0.
    //   N even: convex everywhere (s'' = N(N-1)x^(N-2) >= 0 for all real x).
    //   N odd:  convex on x >= 0, concave on x <= 0. Each branch supports
    //           its own tangent/secant. Mixed-sign interval -> no straight
    //           convex/concave -> skip secant/tangent (caller can still
    //           emit sign cut via the nonneg path above when one side is
    //           sign-determinate).
    const bool intervalAllNonneg = (l >= 0);
    const bool intervalAllNonpos = (u <= 0);
    const bool branchPureConvex = nIsEven || intervalAllNonneg;
    const bool branchPureConcave = !nIsEven && intervalAllNonpos;

    if (!branchPureConvex && !branchPureConcave) {
        // Mixed-sign interval for odd N: don't emit secant/tangent (would be
        // unsound on the wrong branch). Nonneg/nonpos above only fire on
        // sign-determinate intervals. Future Phase 1b can add a two-tangent
        // construction for the inflection-at-0 case.
        return cuts;
    }

    // ------------------------------------------------------------------
    // Cut 2: secant upper bound (convex piece) / lower bound (concave piece).
    //   convex:  s <= ((u^N - l^N) / (u - l)) * (x - l) + l^N
    //          = slope*x + (l^N - slope*l)
    //   concave: s >= same expression (chord lies BELOW the curve on
    //          concave piece, so it's a lower bound).
    // ------------------------------------------------------------------
    if (emitSecant && u != l) {
        mpq_class uN = powQ(u, exponent);
        mpq_class lN = powQ(l, exponent);
        mpq_class slope = (uN - lN) / (u - l);
        mpq_class intercept = lN - slope * l;   // = (l^N * u - u^N * l) / (u - l)
        ZeroLinearConstraint z;
        if (branchPureConvex) {
            // s - slope*x - intercept <= 0
            z.expr.terms.push_back({s.name, mpq_class(1)});
            z.expr.terms.push_back({x, -slope});
            z.expr.constant = -intercept;
            z.rel = Relation::Leq;
            z.debugTag = "power_secant_convex";
        } else {
            // branchPureConcave: -s + slope*x + intercept <= 0
            z.expr.terms.push_back({s.name, mpq_class(-1)});
            z.expr.terms.push_back({x, slope});
            z.expr.constant = intercept;
            z.rel = Relation::Leq;
            z.debugTag = "power_secant_concave";
        }
        z.sort = sort;
        cuts.push_back({std::move(z), boundReasons, z.debugTag});
    }

    // ------------------------------------------------------------------
    // Cut 3: tangent.
    //   convex:  s >= a^N + N*a^(N-1) * (x - a)  (tangent below curve)
    //          encoded as: -s + N*a^(N-1)*x + (a^N - N*a^N) <= 0
    //          = -s + N*a^(N-1)*x - (N-1)*a^N <= 0
    //   concave: s <= a^N + N*a^(N-1) * (x - a)  (tangent above curve)
    //          encoded as: s - N*a^(N-1)*x + (N-1)*a^N <= 0
    // Tangent point a chosen from modelX (LRA candidate) or bound midpoint.
    // For mixed-sign branches we already returned above.
    // ------------------------------------------------------------------
    if (emitTangent) {
        mpq_class a = modelX ? *modelX : (l + u) / 2;
        // Ensure tangent point is on the right branch. If modelX is on the
        // wrong sign-branch for odd N, fall back to bound midpoint of the
        // active branch.
        if (!nIsEven) {
            if (branchPureConvex && a < 0)  a = (l + u) / 2;
            if (branchPureConcave && a > 0) a = (l + u) / 2;
        }
        mpq_class aN     = powQ(a, exponent);
        mpq_class aNm1   = powQ(a, exponent - 1);
        mpq_class slope  = mpq_class(exponent) * aNm1;
        mpq_class shift  = mpq_class(exponent - 1) * aN;   // (N-1)*a^N
        ZeroLinearConstraint z;
        if (branchPureConvex) {
            z.expr.terms.push_back({s.name, mpq_class(-1)});
            z.expr.terms.push_back({x, slope});
            z.expr.constant = -shift;
            z.rel = Relation::Leq;
            z.debugTag = "power_tangent_convex";
        } else {
            z.expr.terms.push_back({s.name, mpq_class(1)});
            z.expr.terms.push_back({x, -slope});
            z.expr.constant = shift;
            z.rel = Relation::Leq;
            z.debugTag = "power_tangent_concave";
        }
        z.sort = sort;
        cuts.push_back({std::move(z), boundReasons, z.debugTag});
    }

    return cuts;
}

} // namespace xolver
