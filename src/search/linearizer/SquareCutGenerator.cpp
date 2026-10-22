#include "search/linearizer/SquareCutGenerator.h"

namespace xolver {

std::vector<LinearCut> SquareCutGenerator::generate(
    const AuxTerm& s,
    const std::string& x,
    const LinearizationBounds& xBounds,
    SatLit nonlinearReason,
    const std::optional<mpq_class>& modelX,
    SortKind sort) {

    std::vector<LinearCut> cuts;

    // Cut 1: Nonnegativity (s >= 0), i.e. -s <= 0
    {
        ZeroLinearConstraint z;
        z.expr.terms.push_back({s.name, mpq_class(-1)});
        z.rel = Relation::Leq;
        z.sort = sort;
        z.debugTag = "square_nonneg";
        cuts.push_back({std::move(z), {nonlinearReason}, "square_nonneg"});
    }

    const bool finiteBounds = xBounds.hasFiniteCompleteBounds();
    if (finiteBounds) {
        const mpq_class& l = xBounds.lower;
        const mpq_class& u = xBounds.upper;
        std::vector<SatLit> reasons{nonlinearReason};
        reasons.insert(reasons.end(), xBounds.lowerReasons.begin(), xBounds.lowerReasons.end());
        reasons.insert(reasons.end(), xBounds.upperReasons.begin(), xBounds.upperReasons.end());
        ZeroLinearConstraint z;
        z.expr.terms.push_back({s.name, mpq_class(1)});
        z.expr.terms.push_back({x, -(l + u)});
        z.expr.constant = l * u;
        z.rel = Relation::Leq;
        z.sort = sort;
        z.debugTag = "square_secant";
        cuts.push_back({std::move(z), std::move(reasons), "square_secant"});
    }

    // Cut 3: Tangent lower bound
    //   -s + 2a*x - a^2 <= 0
    if (modelX || finiteBounds) {
        mpq_class a = modelX ? *modelX : (xBounds.lower + xBounds.upper) / 2;
        mpq_class twoA = 2 * a;
        ZeroLinearConstraint z;
        z.expr.terms.push_back({s.name, mpq_class(-1)});
        z.expr.terms.push_back({x, twoA});
        z.expr.constant = -(a * a);
        z.rel = Relation::Leq;
        z.sort = sort;
        z.debugTag = "square_tangent";
        cuts.push_back({std::move(z), {nonlinearReason}, "square_tangent"});
    }

    return cuts;
}

} // namespace xolver
