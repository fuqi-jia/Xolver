#pragma once

#include "theory/arith/nra/CdcacTypes.h"
#include "theory/arith/nra/CdcacConstraint.h"
#include <vector>
#include <memory>

namespace nlcolver {

class PolynomialKernel;

// ------------------------------------------------------------------
// V6: Variable ordering heuristic
// ------------------------------------------------------------------
enum class VarOrderStrategy : uint8_t {
    InputOrder,       // preserve input/SMT-LIB declaration order
    DegreeBased,      // highest total degree first
    OccurrenceBased,  // most frequent first
    SOTDLike,         // sum of total degrees (Collins-style)
    BrownHeuristic    // Brown's variable ordering heuristic
};

struct VarOrderHeuristicResult {
    std::vector<VarId> order;
    bool success = false;
};

class VarOrderHeuristic {
public:
    explicit VarOrderHeuristic(PolynomialKernel* kernel);

    VarOrderHeuristicResult compute(
        const std::vector<PolyId>& polys,
        VarOrderStrategy strategy = VarOrderStrategy::InputOrder);

    // Convenience: compute from constraints
    VarOrderHeuristicResult computeFromConstraints(
        const std::vector<CdcacConstraint>& constraints,
        VarOrderStrategy strategy = VarOrderStrategy::InputOrder);

private:
    PolynomialKernel* kernel_;

    VarOrderHeuristicResult inputOrder(const std::vector<VarId>& vars);
    VarOrderHeuristicResult degreeBased(const std::vector<PolyId>& polys, const std::vector<VarId>& vars);
    VarOrderHeuristicResult occurrenceBased(const std::vector<PolyId>& polys, const std::vector<VarId>& vars);
    VarOrderHeuristicResult sotdLike(const std::vector<PolyId>& polys, const std::vector<VarId>& vars);
    VarOrderHeuristicResult brownHeuristic(const std::vector<PolyId>& polys, const std::vector<VarId>& vars);
};

} // namespace nlcolver
