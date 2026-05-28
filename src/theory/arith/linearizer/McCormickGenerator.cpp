#include "theory/arith/linearizer/McCormickGenerator.h"

namespace xolver {

std::vector<LinearCut> McCormickGenerator::generate(
    const AuxTerm& t,
    const std::string& x, const std::string& y,
    const BoundInfo& xBounds,
    const BoundInfo& yBounds,
    SatLit nonlinearReason,
    SortKind sort) {

    if (!xBounds.hasFiniteCompleteBounds() || !yBounds.hasFiniteCompleteBounds()) {
        return {};
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
