#include "search/nra/reasoners/NlaCutsRunner.h"


namespace xolver {
namespace nla {

NlaCutsRunner::NlaCutsRunner(PolynomialKernel& kernel)
    : kernel_(kernel), gen_(kernel) {}

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
    return out;
}

} // namespace nla
} // namespace xolver
