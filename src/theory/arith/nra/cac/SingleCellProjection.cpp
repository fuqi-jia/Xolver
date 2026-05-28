#include "theory/arith/nra/cac/SingleCellProjection.h"

#include "theory/arith/nra/projection/LazardProjectionOperator.h"

#include <string>
#include <unordered_set>

namespace xolver {

namespace {
// Canonical key (up to a rational unit) for deduping output polynomials, so a
// coefficient and a discriminant that are proportional collapse to one boundary.
std::string unitKey(RationalPolynomial p) {
    p.normalize();
    if (!p.isZero()) {
        const mpq_class lead = p.terms().rbegin()->second;
        if (lead != 0 && lead != 1) { p *= (mpq_class(1) / lead); p.normalize(); }
    }
    std::string key;
    for (const auto& [mon, coeff] : p.terms()) {
        key += coeff.get_str() + ":";
        for (const auto& [v, e] : mon) key += std::to_string(v) + "^" + std::to_string(e) + ";";
        key += "|";
    }
    return key;
}
} // namespace

CharacterizationResult characterize(const std::vector<RationalPolynomial>& cellPolys,
                                    VarId elimVar,
                                    PolynomialKernel* kernel) {
    CharacterizationResult out;

    LazardOpResult r = lazardProjectStep(cellPolys, elimVar,
                                         LazardProjectionConfig(), kernel);
    if (!r.complete) {
        out.complete = false;
        return out;   // caller ⇒ Unknown; never UNSAT on an incomplete characterization
    }

    std::unordered_set<std::string> seenBoundary, seenDownward;
    for (const auto& item : r.items) {
        RationalPolynomial p = item.poly;
        p.normalize();
        if (p.isZero() || p.isConstant()) continue;   // constants delineate nothing
        if (p.degree(elimVar) >= 1) {
            if (seenBoundary.insert(unitKey(p)).second) out.boundaryPolys.push_back(std::move(p));
        } else {
            if (seenDownward.insert(unitKey(p)).second) out.downwardPolys.push_back(std::move(p));
        }
    }
    return out;
}

} // namespace xolver
