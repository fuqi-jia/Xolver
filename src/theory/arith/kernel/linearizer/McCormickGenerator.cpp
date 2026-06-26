#include "theory/arith/kernel/linearizer/McCormickGenerator.h"
#include "util/EnvParam.h"

namespace xolver {

std::vector<LinearCut> McCormickGenerator::generate(
    const AuxTerm& t,
    const std::string& x, const std::string& y,
    const BoundInfo& xBounds,
    const BoundInfo& yBounds,
    SatLit nonlinearReason,
    SortKind sort) {

    std::vector<LinearCut> cutsEarly;

    // Family 0 (NEW) — sign-only cut for sign-pinned factors.
    // For `t = x · y` with x sign-pinned (lo > 0 or hi < 0) and y same,
    // the product's strict sign is determined. Emit `t > 0` or `t < 0`.
    // Independent of upper bounds — closes the cvc5 NL_COMPARISON gap.
    {
        auto signOf = [](const BoundInfo& b) -> int {
            if (b.hasLower && b.lower > 0) return 1;
            if (b.hasUpper && b.upper < 0) return -1;
            return 0;
        };
        int xs = signOf(xBounds);
        int ys = signOf(yBounds);
        if (xs != 0 && ys != 0) {
            int prodSign = xs * ys;
            std::vector<SatLit> signReasons{nonlinearReason};
            if (xs > 0) signReasons.insert(signReasons.end(),
                                           xBounds.lowerReasons.begin(),
                                           xBounds.lowerReasons.end());
            else        signReasons.insert(signReasons.end(),
                                           xBounds.upperReasons.begin(),
                                           xBounds.upperReasons.end());
            if (ys > 0) signReasons.insert(signReasons.end(),
                                           yBounds.lowerReasons.begin(),
                                           yBounds.lowerReasons.end());
            else        signReasons.insert(signReasons.end(),
                                           yBounds.upperReasons.begin(),
                                           yBounds.upperReasons.end());
            ZeroLinearConstraint z;
            z.expr.terms.push_back({t.name, mpq_class(prodSign > 0 ? -1 : 1)});
            z.expr.constant = 0;
            z.rel = Relation::Lt;
            z.sort = sort;
            z.debugTag = "mccormick_sign_only";
            cutsEarly.push_back({std::move(z), signReasons, "mccormick_sign_only"});
        }
    }

    // ── Partial-bounds extension (XOLVER_NRA_MCCORMICK_PARTIAL, default-OFF) ──
    // Each McCormick envelope cut follows from ONE sign fact (x−a)(y−b) ⪋ 0 and so
    // needs only TWO of the four bounds, not all four:
    //   (x−lx)(y−ly) ≥ 0 ⟹ t ≥ lx·y + ly·x − lx·ly      [needs lx, ly]
    //   (x−ux)(y−uy) ≥ 0 ⟹ t ≥ ux·y + uy·x − ux·uy      [needs ux, uy]
    //   (x−ux)(y−ly) ≤ 0 ⟹ t ≤ ux·y + ly·x − ux·ly      [needs ux, ly]
    //   (x−lx)(y−uy) ≤ 0 ⟹ t ≤ lx·y + uy·x − lx·uy      [needs lx, uy]
    // When the box is only partially bounded (the complete-bounds path below bails),
    // emit whichever cuts have BOTH their required bounds present AND reason-complete.
    // Reason-completeness is load-bearing: a cut citing an incomplete reason set would
    // be valid only under unrecorded assumptions ⇒ an unsound lemma.
    if (!xBounds.hasFiniteCompleteBounds() || !yBounds.hasFiniteCompleteBounds()) {
        if (env::flag("XOLVER_NRA_MCCORMICK_PARTIAL")) {
            const bool xLo = xBounds.hasLower && (xBounds.lowerIsGlobal || xBounds.lowerReasonComplete);
            const bool xHi = xBounds.hasUpper && (xBounds.upperIsGlobal || xBounds.upperReasonComplete);
            const bool yLo = yBounds.hasLower && (yBounds.lowerIsGlobal || yBounds.lowerReasonComplete);
            const bool yHi = yBounds.hasUpper && (yBounds.upperIsGlobal || yBounds.upperReasonComplete);
            auto reasons = [&](const std::vector<SatLit>& a, const std::vector<SatLit>& b) {
                std::vector<SatLit> r{nonlinearReason};
                r.insert(r.end(), a.begin(), a.end());
                r.insert(r.end(), b.begin(), b.end());
                return r;
            };
            auto emit = [&](mpq_class tc, mpq_class yc, mpq_class xc, mpq_class konst,
                            std::vector<SatLit> rs, const char* tag) {
                ZeroLinearConstraint z;
                z.expr.terms.push_back({t.name, tc});
                z.expr.terms.push_back({y, yc});
                z.expr.terms.push_back({x, xc});
                z.expr.constant = konst;
                z.rel = Relation::Leq;
                z.sort = sort;
                z.debugTag = tag;
                cutsEarly.push_back({std::move(z), std::move(rs), tag});
            };
            if (xLo && yLo)   // t ≥ lx·y + ly·x − lx·ly
                emit(-1, xBounds.lower, yBounds.lower, -(xBounds.lower * yBounds.lower),
                     reasons(xBounds.lowerReasons, yBounds.lowerReasons), "mccormick_partial_lower1");
            if (xHi && yHi)   // t ≥ ux·y + uy·x − ux·uy
                emit(-1, xBounds.upper, yBounds.upper, -(xBounds.upper * yBounds.upper),
                     reasons(xBounds.upperReasons, yBounds.upperReasons), "mccormick_partial_lower2");
            if (xHi && yLo)   // t ≤ ux·y + ly·x − ux·ly
                emit(1, -xBounds.upper, -yBounds.lower, xBounds.upper * yBounds.lower,
                     reasons(xBounds.upperReasons, yBounds.lowerReasons), "mccormick_partial_upper1");
            if (xLo && yHi)   // t ≤ lx·y + uy·x − lx·uy
                emit(1, -xBounds.lower, -yBounds.upper, xBounds.lower * yBounds.upper,
                     reasons(xBounds.lowerReasons, yBounds.upperReasons), "mccormick_partial_upper2");
        }
        return cutsEarly;
    }

    const mpq_class& lx = xBounds.lower;
    const mpq_class& ux = xBounds.upper;
    const mpq_class& ly = yBounds.lower;
    const mpq_class& uy = yBounds.upper;

    std::vector<SatLit> baseReasons;
    baseReasons.push_back(nonlinearReason);
    baseReasons.insert(baseReasons.end(),
                       xBounds.lowerReasons.begin(), xBounds.lowerReasons.end());
    baseReasons.insert(baseReasons.end(),
                       xBounds.upperReasons.begin(), xBounds.upperReasons.end());
    baseReasons.insert(baseReasons.end(),
                       yBounds.lowerReasons.begin(), yBounds.lowerReasons.end());
    baseReasons.insert(baseReasons.end(),
                       yBounds.upperReasons.begin(), yBounds.upperReasons.end());

    std::vector<LinearCut> cuts;

    // Cut 1: -t + lx*y + ly*x - lx*ly <= 0
    {
        ZeroLinearConstraint z;
        z.expr.terms.push_back({t.name, mpq_class(-1)});
        z.expr.terms.push_back({y, lx});
        z.expr.terms.push_back({x, ly});
        z.expr.constant = -(lx * ly);
        z.rel = Relation::Leq;
        z.sort = sort;
        z.debugTag = "mccormick_lower1";
        cuts.push_back({std::move(z), baseReasons, "mccormick_lower1"});
    }

    // Cut 2: -t + ux*y + uy*x - ux*uy <= 0
    {
        ZeroLinearConstraint z;
        z.expr.terms.push_back({t.name, mpq_class(-1)});
        z.expr.terms.push_back({y, ux});
        z.expr.terms.push_back({x, uy});
        z.expr.constant = -(ux * uy);
        z.rel = Relation::Leq;
        z.sort = sort;
        z.debugTag = "mccormick_lower2";
        cuts.push_back({std::move(z), baseReasons, "mccormick_lower2"});
    }

    // Cut 3: t - ux*y - ly*x + ux*ly <= 0
    {
        ZeroLinearConstraint z;
        z.expr.terms.push_back({t.name, mpq_class(1)});
        z.expr.terms.push_back({y, -ux});
        z.expr.terms.push_back({x, -ly});
        z.expr.constant = ux * ly;
        z.rel = Relation::Leq;
        z.sort = sort;
        z.debugTag = "mccormick_upper1";
        cuts.push_back({std::move(z), baseReasons, "mccormick_upper1"});
    }

    // Cut 4: t - lx*y - uy*x + lx*uy <= 0
    {
        ZeroLinearConstraint z;
        z.expr.terms.push_back({t.name, mpq_class(1)});
        z.expr.terms.push_back({y, -lx});
        z.expr.terms.push_back({x, -uy});
        z.expr.constant = lx * uy;
        z.rel = Relation::Leq;
        z.sort = sort;
        z.debugTag = "mccormick_upper2";
        cuts.push_back({std::move(z), baseReasons, "mccormick_upper2"});
    }

    return cuts;
}

} // namespace xolver
