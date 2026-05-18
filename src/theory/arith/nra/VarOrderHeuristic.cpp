#include "theory/arith/nra/VarOrderHeuristic.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include <algorithm>
#include <unordered_map>
#include <unordered_set>

namespace nlcolver {

VarOrderHeuristic::VarOrderHeuristic(PolynomialKernel* kernel)
    : kernel_(kernel) {}

VarOrderHeuristicResult VarOrderHeuristic::compute(
    const std::vector<PolyId>& polys,
    VarOrderStrategy strategy) {

    if (!kernel_) return {{}, false};

    // Collect all variables appearing in polynomials
    std::unordered_set<VarId> varSet;
    for (auto p : polys) {
        auto vars = kernel_->variables(p);
        for (const auto& vname : vars) {
            varSet.insert(kernel_->getOrCreateVar(vname));
        }
    }
    std::vector<VarId> vars(varSet.begin(), varSet.end());

    switch (strategy) {
        case VarOrderStrategy::InputOrder:
            return inputOrder(vars);
        case VarOrderStrategy::DegreeBased:
            return degreeBased(polys, vars);
        case VarOrderStrategy::OccurrenceBased:
            return occurrenceBased(polys, vars);
        case VarOrderStrategy::SOTDLike:
            return sotdLike(polys, vars);
        case VarOrderStrategy::BrownHeuristic:
            return brownHeuristic(polys, vars);
    }
    return inputOrder(vars);
}

VarOrderHeuristicResult VarOrderHeuristic::computeFromConstraints(
    const std::vector<CdcacConstraint>& constraints,
    VarOrderStrategy strategy) {

    std::vector<PolyId> polys;
    polys.reserve(constraints.size());
    for (size_t i = 0; i < constraints.size(); ++i) {
        polys.push_back(constraints[i].poly);
    }
    return compute(polys, strategy);
}

VarOrderHeuristicResult VarOrderHeuristic::inputOrder(const std::vector<VarId>& vars) {
    VarOrderHeuristicResult result;
    result.order = vars;
    // Sort by variable ID (which roughly corresponds to input order)
    std::sort(result.order.begin(), result.order.end(),
              [](VarId a, VarId b) { return a < b; });
    result.success = true;
    return result;
}

VarOrderHeuristicResult VarOrderHeuristic::degreeBased(
    const std::vector<PolyId>& polys,
    const std::vector<VarId>& vars) {

    VarOrderHeuristicResult result;
    std::unordered_map<VarId, int> degreeSum;
    for (auto p : polys) {
        for (auto v : vars) {
            auto d = kernel_->degree(p, kernel_->varName(v));
            if (d) degreeSum[v] += *d;
        }
    }
    result.order = vars;
    std::sort(result.order.begin(), result.order.end(),
              [&degreeSum](VarId a, VarId b) {
                  return degreeSum[a] > degreeSum[b];
              });
    result.success = true;
    return result;
}

VarOrderHeuristicResult VarOrderHeuristic::occurrenceBased(
    const std::vector<PolyId>& polys,
    const std::vector<VarId>& vars) {

    VarOrderHeuristicResult result;
    std::unordered_map<VarId, int> count;
    for (auto p : polys) {
        auto pvars = kernel_->variables(p);
        std::unordered_set<std::string> seen(pvars.begin(), pvars.end());
        for (const auto& vname : seen) {
            count[kernel_->getOrCreateVar(vname)]++;
        }
    }
    result.order = vars;
    std::sort(result.order.begin(), result.order.end(),
              [&count](VarId a, VarId b) {
                  return count[a] > count[b];
              });
    result.success = true;
    return result;
}

VarOrderHeuristicResult VarOrderHeuristic::sotdLike(
    const std::vector<PolyId>& polys,
    const std::vector<VarId>& vars) {

    // V6 skeleton: SOTD-like ordering (sum of total degrees per variable).
    // Full implementation would compute exact SOTD across all projection steps.
    return degreeBased(polys, vars);
}

VarOrderHeuristicResult VarOrderHeuristic::brownHeuristic(
    const std::vector<PolyId>& polys,
    const std::vector<VarId>& vars) {

    // V6 skeleton: Brown's heuristic minimizes projection set size.
    // Full implementation would require estimating projection cost per variable.
    return degreeBased(polys, vars);
}

} // namespace nlcolver
