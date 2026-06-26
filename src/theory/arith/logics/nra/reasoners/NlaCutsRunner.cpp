#include "theory/arith/logics/nra/reasoners/NlaCutsRunner.h"

#include <cstdlib>

namespace xolver {
namespace nla {

NlaCutsRunner::NlaCutsRunner(PolynomialKernel& kernel)
    : kernel_(kernel), gen_(kernel) {}

bool NlaCutsRunner::enabled() const {
    // Read once, cache. Either NRA-side (CDCAC hook) or NIA-side (Phase
    // C-3 hook) flag enables the runner. The runner itself is theory-
    // agnostic; the caller's gate decides when to invoke and which
    // env var anchors it. Returning true when EITHER is set lets one
    // generator implementation serve both lanes.
    static const bool en = [] {
        const char* nra = std::getenv("XOLVER_NRA_NLA_CUTS");
        const char* nia = std::getenv("XOLVER_NIA_NLA_CUTS");
        bool nraOn = nra && *nra && *nra != '0';
        bool niaOn = nia && *nia && *nia != '0';
        return nraOn || niaOn;
    }();
    return en;
}

std::vector<NlaCut> NlaCutsRunner::runShapeCuts(
        const std::vector<VarInterval>& vars, std::size_t maxPairs) {
    std::vector<NlaCut> out;
    if (!enabled()) return out;

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
    if (!enabled()) return out;
    out.reserve(points.size());
    for (const auto& [varPoly, m] : points) {
        out.push_back(gen_.tangentSquare(varPoly, m, reasons));
    }
    return out;
}

} // namespace nla
} // namespace xolver
