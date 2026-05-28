#pragma once
#include "theory/arith/poly/PolynomialKernel.h"
#include "theory/arith/nra/core/CdcacTypes.h"
#include "theory/arith/nra/core/CdcacConstraint.h" // CdcacConstraint, Relation, SatLit
#include "expr/types.h"
#include <unordered_map>
#include <vector>

namespace xolver {

class PolyStructureFacts {
public:
    int linearizationGain(VarId v) const { return get(linGain_, v); }
    int nonlinearConnectivity(VarId v) const { return get(connect_, v); }
    int maxDegree(VarId v) const { return get(maxDeg_, v); }

    std::unordered_map<VarId,int> linGain_, connect_, maxDeg_;
private:
    static int get(const std::unordered_map<VarId,int>& m, VarId v) {
        auto it = m.find(v); return it == m.end() ? 0 : it->second;
    }
};

PolyStructureFacts computeStructureFacts(
    const PolynomialKernel& kernel,
    const std::vector<CdcacConstraint>& nonlinearConstraints);

} // namespace xolver
