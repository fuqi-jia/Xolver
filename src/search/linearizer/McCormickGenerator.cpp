#include "search/linearizer/McCormickGenerator.h"
#include <algorithm>

namespace xolver {

std::vector<LinearCut> McCormickGenerator::generate(
    const AuxTerm& t,
    const std::string& x, const std::string& y,
    const LinearizationBounds& xb, const LinearizationBounds& yb,
    SatLit nonlinearReason, SortKind sort) {
    auto lower = [](const LinearizationBounds& b) {
        return b.hasLower && (b.lowerIsGlobal || b.lowerReasonComplete);
    };
    auto upper = [](const LinearizationBounds& b) {
        return b.hasUpper && (b.upperIsGlobal || b.upperReasonComplete);
    };
    auto openSign = [&](const LinearizationBounds& b) {
        if (lower(b) && b.lower == 0 && b.lowerStrict) return 1;
        if (upper(b) && b.upper == 0 && b.upperStrict) return -1;
        return 0;
    };
    const int xs = openSign(xb), ys = openSign(yb);
    auto reasons = [&](const std::vector<SatLit>& first, const std::vector<SatLit>& second) {
        std::vector<SatLit> result{nonlinearReason};
        for (const auto* sources : {&first, &second})
            for (auto premise : *sources)
                if (std::find(result.begin(), result.end(), premise) == result.end()) result.push_back(premise);
        return result;
    };
    std::vector<LinearCut> cuts;
    auto face = [&](const mpq_class& bx, const mpq_class& by, bool over,
                    const std::vector<SatLit>& whyX, const std::vector<SatLit>& whyY,
                    const char* tag) {
        // The strict sign below subsumes this closed zero face.
        if (xs && ys && bx == 0 && by == 0 && over == (xs != ys)) return;
        ZeroLinearConstraint constraint;
        // Under-estimator: -t + bx*y + by*x - bx*by <= 0.
        // Each face needs only its own pair of justified endpoints.
        const mpq_class sign = over ? 1 : -1;
        constraint.expr.terms = {{t.name, sign}, {y, -sign * bx}, {x, -sign * by}};
        constraint.expr.constant = sign * bx * by;
        constraint.rel = Relation::Leq;
        constraint.sort = sort;
        constraint.debugTag = tag;
        cuts.push_back({std::move(constraint), reasons(whyX, whyY), tag});
    };
    if (lower(xb) && lower(yb))
        face(xb.lower, yb.lower, false, xb.lowerReasons, yb.lowerReasons, "mccormick_lower1");
    if (upper(xb) && upper(yb))
        face(xb.upper, yb.upper, false, xb.upperReasons, yb.upperReasons, "mccormick_lower2");
    if (upper(xb) && lower(yb))
        face(xb.upper, yb.lower, true, xb.upperReasons, yb.lowerReasons, "mccormick_upper1");
    if (lower(xb) && upper(yb))
        face(xb.lower, yb.upper, true, xb.lowerReasons, yb.upperReasons, "mccormick_upper2");

    // Two open zero endpoints prove the strict product sign over the reals.
    // No integer unit gap is applied to a real endpoint.
    if (xs && ys) {
        ZeroLinearConstraint constraint;
        constraint.expr.terms = {{t.name, mpq_class(xs == ys ? -1 : 1)}};
        constraint.rel = Relation::Lt;
        constraint.sort = sort;
        constraint.debugTag = "mccormick_strict_sign";
        cuts.push_back({std::move(constraint),
            reasons(xs > 0 ? xb.lowerReasons : xb.upperReasons,
                    ys > 0 ? yb.lowerReasons : yb.upperReasons), "mccormick_strict_sign"});
    }
    return cuts;
}

} // namespace xolver
