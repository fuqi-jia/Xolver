#pragma once

#include "theory/arith/nra/CdcacTypes.h"
#include "theory/arith/nra/CdcacConstraint.h"
#include "theory/arith/nra/AlgebraBackend.h"
#include "theory/arith/nra/CoveringManager.h"
#include "theory/arith/nra/ReasonManager.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include <vector>

namespace nlcolver {

/**
 * CDCAC recursive covering/search algorithm core.
 *
 * Does NOT depend on CdcacSolver's private types.
 * Operates purely on CdcacInput / CdcacConstraint.
 */
class CdcacCore {
public:
    CdcacCore(PolynomialKernel* kernel, AlgebraBackend* algebra);

    CdcacResult solve(const CdcacInput& input);

private:
    CdcacResult solveUnivariate(const CdcacInput& input);
    CdcacResult solveLevel(int k, SamplePoint& prefix, const CdcacInput& input);
    CdcacResult checkFullSample(const SamplePoint& sample, const CdcacInput& input);

    Cell buildLeafConflictCell(const CdcacConstraint& c, const SamplePoint& sample, VarId var);
    Cell generalizeConflictCell(int k, const RealAlg& sample, const CdcacResult& childConflict, const CdcacInput& input);

    bool relationHolds(Sign s, Relation rel) const;

    std::optional<RootSet> mergeRoots(const std::vector<RootSet>& rootSets);

private:
    PolynomialKernel* kernel_;
    AlgebraBackend* algebra_;
};

} // namespace nlcolver
