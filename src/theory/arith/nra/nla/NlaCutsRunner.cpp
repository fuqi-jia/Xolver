#include "theory/arith/nra/nla/NlaCutsRunner.h"

#include <cstdlib>

namespace xolver {
namespace nla {

NlaCutsRunner::NlaCutsRunner(PolynomialKernel& kernel)
    : kernel_(kernel), gen_(kernel) {}

bool NlaCutsRunner::enabled() const {
    // Read once, cache. The runner is constructed per solver instance
    // (or per check call); the flag intent is per-solver-run-anchored,
    // matching the existing env-gated lever style in NiaSolver /
    // NraSolver.
    static const bool en = [] {
        const char* e = std::getenv("XOLVER_NRA_NLA_CUTS");
        return e && *e && *e != '0';
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
