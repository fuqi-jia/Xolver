#include "theory/arith/nra/simplex/VarOrderSelector.h"
#include "theory/arith/nra/simplex/NraLinearExtractor.h"
#include "theory/arith/nra/simplex/SimplexTableauFacts.h"
#include "theory/arith/nra/simplex/PolyStructureFacts.h"
#include <algorithm>
#include <optional>
#include <unordered_map>

namespace xolver {

std::vector<std::string> computeCdcacVarOrder(
    const PolynomialKernel& kernel,
    const std::vector<CdcacConstraint>& constraints,
    const std::vector<std::string>& varNames) {
    auto cc = classifyConstraints(kernel, constraints);
    SimplexTableauFacts tf = computeSimplexTableauFacts(kernel, cc.linear);
    PolyStructureFacts  sf = computeStructureFacts(kernel, cc.nonlinear);

    // Primary key: total-degree sum per variable (same as XOLVER_NRA_VARORDER).
    std::unordered_map<std::string, int> degSum;
    for (const auto& name : varNames) degSum[name] = 0;
    for (const auto& c : constraints)
        for (const auto& name : varNames)
            if (auto d = kernel.degree(c.poly, name)) degSum[name] += *d;

    struct Scored { std::string name; int origPos; int deg; double front; };
    std::vector<Scored> v;
    v.reserve(varNames.size());
    for (size_t i = 0; i < varNames.size(); ++i) {
        // Look up the EXISTING VarId (const-correct: getOrCreateVar is non-const,
        // and ordering must never mint new variables). Names come from the active
        // constraints, so findVar succeeds; a miss => neutral frontScore.
        std::optional<VarId> idOpt = kernel.findVar(varNames[i]);
        if (!idOpt) { v.push_back({ varNames[i], (int)i, degSum[varNames[i]], 0.0 }); continue; }
        VarId id = *idOpt;
        // frontScore: structural linearization dominates; tableau facts are weak
        // tie-breaks (heuristic-only; never affect soundness).
        double front =
              3.0  * sf.linearizationGain(id)
            + 1.0  * sf.nonlinearConnectivity(id)
            + 0.5  * (tf.isFixed(id) ? 1 : 0)
            + 0.5  * tf.tightRowParticipation(id)
            + 0.25 * tf.boundedness(id)
            + 0.25 * (tf.isBasic(id) ? 1 : 0)
            - 1.0  * std::max(0, sf.maxDegree(id) - 1);   // algebraicComplexityPenalty
        v.push_back({ varNames[i], (int)i, degSum[varNames[i]], front });
    }
    // Ascending degree; within equal degree, ascending frontScore (higher
    // frontScore => later); final tie-break original position.
    std::stable_sort(v.begin(), v.end(), [](const Scored& a, const Scored& b) {
        if (a.deg != b.deg)     return a.deg   < b.deg;
        if (a.front != b.front) return a.front < b.front;
        return a.origPos < b.origPos;
    });
    std::vector<std::string> out;
    out.reserve(v.size());
    for (const auto& s : v) out.push_back(s.name);
    return out;
}

} // namespace xolver
