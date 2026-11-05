#include "search/nra/reasoners/NlaCutsRunner.h"
#include <algorithm>
#include <map>

namespace xolver {
namespace nla {

NlaCutsRunner::NlaCutsRunner(PolynomialKernel& kernel)
    : kernel_(kernel), gen_(kernel) {}

void NlaCutsRunner::sharePolynomials(std::vector<NlaCut>& cuts) {
    for (auto& cut : cuts) {
        const auto polynomial = RationalPolynomial::fromPolyId(cut.poly, kernel_);
        if (!polynomial) continue;
        PolynomialShape shape(polynomial->terms().begin(), polynomial->terms().end());
        const auto [found, inserted] = polynomials_.try_emplace(std::move(shape), cut.poly);
        (void)inserted;
        cut.poly = found->second;
    }
}

std::vector<VarInterval> NlaCutsRunner::collectIntervals(
        const std::vector<SignRefuteConstraint>& constraints) {
    struct Endpoint { mpq_class value; SatLit reason; };
    struct Bounds { std::optional<Endpoint> lower, upper; };
    std::map<VarId, Bounds> ranges;
    for (const auto& constraint : constraints) {
        if (constraint.rel == Relation::Neq || !constraint.reason.var) continue;
        std::optional<VarId> variable;
        mpq_class coefficient = 0, constant = 0;
        bool linear = true;
        for (const auto& [monomial, value] : constraint.poly.terms()) {
            if (monomial.empty()) constant += value;
            else if (!variable && monomial.size() == 1 && monomial.front().second == 1) {
                variable = monomial.front().first;
                coefficient = value;
            } else { linear = false; break; }
        }
        if (!linear || !variable || coefficient == 0) continue;
        const mpq_class value = -constant / coefficient;
        auto relation = constraint.rel;
        if (coefficient < 0) {
            switch (relation) {
                case Relation::Leq: relation = Relation::Geq; break;
                case Relation::Lt: relation = Relation::Gt; break;
                case Relation::Geq: relation = Relation::Leq; break;
                case Relation::Gt: relation = Relation::Lt; break;
                default: break;
            }
        }
        auto& range = ranges[*variable];
        if (relation == Relation::Eq || relation == Relation::Geq || relation == Relation::Gt)
            if (!range.lower || value > range.lower->value)
                range.lower = Endpoint{value, constraint.reason};
        if (relation == Relation::Eq || relation == Relation::Leq || relation == Relation::Lt)
            if (!range.upper || value < range.upper->value)
                range.upper = Endpoint{value, constraint.reason};
    }
    std::vector<VarInterval> result;
    result.reserve(ranges.size());
    for (const auto& [variable, range] : ranges) {
        VarInterval interval;
        interval.varPoly = kernel_.mkVar(variable);
        if (range.lower) {
            interval.lo = range.lower->value;
            interval.reasons.push_back(range.lower->reason);
        }
        if (range.upper) {
            interval.hi = range.upper->value;
            if (std::find(interval.reasons.begin(), interval.reasons.end(), range.upper->reason) == interval.reasons.end())
                interval.reasons.push_back(range.upper->reason);
        }
        result.push_back(std::move(interval));
    }
    return result;
}

std::vector<NlaCut> NlaCutsRunner::runShapeCuts(
        const std::vector<VarInterval>& vars, std::size_t maxPairs) {
    std::vector<NlaCut> out;

    // Per-variable square cuts.
    for (const VarInterval& v : vars) {
        auto sq = gen_.monotonicitySquare(v);
        for (auto& c : sq) out.push_back(std::move(c));
    }

    // Pairwise product cuts, capped.
    std::size_t pairsDone = 0;
    for (std::size_t i = 0; i < vars.size() && pairsDone < maxPairs; ++i) {
        for (std::size_t j = i + 1; j < vars.size() && pairsDone < maxPairs;
             ++j) {
            auto prod = gen_.monotonicityProduct(vars[i], vars[j]);
            for (auto& c : prod) out.push_back(std::move(c));
            auto mc = gen_.mccormickBilinear(vars[i], vars[j]);
            for (auto& c : mc) out.push_back(std::move(c));
            ++pairsDone;
        }
    }

    sharePolynomials(out);
    return out;
}

std::vector<NlaCut> NlaCutsRunner::runTangents(
        const std::vector<std::pair<PolyId, mpq_class>>& points,
        const std::vector<SatLit>& reasons) {
    std::vector<NlaCut> out;
    out.reserve(points.size());
    for (const auto& [varPoly, m] : points) {
        out.push_back(gen_.tangentSquare(varPoly, m, reasons));
    }
    sharePolynomials(out);
    return out;
}

} // namespace nla
} // namespace xolver
