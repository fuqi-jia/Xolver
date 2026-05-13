#include "theory/arith/linearizer/SquareCutGenerator.h"

namespace nlcolver {

std::vector<LinearCut> SquareCutGenerator::generate(
    const AuxTerm& s,
    const std::string& x,
    const BoundInfo& xBounds,
    SatLit nonlinearReason,
    const std::optional<mpq_class>& modelX,
    bool emitNonneg,
    bool emitSecant,
    bool emitTangent) {

    std::vector<LinearCut> cuts;
    SortKind sort = SortKind::Int; // V1 only handles integer squares

    // Cut 1: Nonnegativity (s >= 0), i.e. -s <= 0
    if (emitNonneg) {
        ZeroLinearConstraint z;
        z.expr.terms.push_back({s.name, mpq_class(-1)});
        z.rel = Relation::Leq;
        z.sort = sort;
        z.debugTag = "square_nonneg";
        cuts.push_back({std::move(z), {nonlinearReason}, "square_nonneg"});
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

    // Cut 2: Secant upper bound
    //   s - (l+u)*x + l*u <= 0
    if (emitSecant) {
        mpq_class sum = l + u;
        ZeroLinearConstraint z;
        z.expr.terms.push_back({s.name, mpq_class(1)});
        z.expr.terms.push_back({x, -sum});
        z.expr.constant = l * u;
        z.rel = Relation::Leq;
        z.sort = sort;
        z.debugTag = "square_secant";
        cuts.push_back({std::move(z), boundReasons, "square_secant"});
    }

    // Cut 3: Tangent lower bound
    //   -s + 2a*x - a^2 <= 0
    if (emitTangent) {
        mpq_class a = modelX ? *modelX : (l + u) / 2;
        mpq_class twoA = 2 * a;
        ZeroLinearConstraint z;
        z.expr.terms.push_back({s.name, mpq_class(-1)});
        z.expr.terms.push_back({x, twoA});
        z.expr.constant = -(a * a);
        z.rel = Relation::Leq;
        z.sort = sort;
        z.debugTag = "square_tangent";
        cuts.push_back({std::move(z), boundReasons, "square_tangent"});
    }

    return cuts;
}

} // namespace nlcolver
