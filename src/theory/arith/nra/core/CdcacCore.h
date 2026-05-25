#pragma once

#include "theory/arith/nra/core/CdcacTypes.h"
#include "theory/arith/nra/core/CdcacConstraint.h"
#include "theory/arith/nra/backend/AlgebraBackend.h"
#include "theory/arith/nra/engine/CoveringManager.h"
#include "theory/arith/nra/engine/ReasonManager.h"
#include "theory/arith/nra/projection/ProjectionPolicy.h"
#include "theory/arith/nra/projection/ProjectionClosure.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include <vector>
#include <memory>

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

    /**
     * V4: Set the projection policy. If not set, defaults to CollinsConservative.
     */
    void setProjectionPolicy(std::unique_ptr<ProjectionPolicy> policy);

private:
    CdcacResult solveUnivariate(const CdcacInput& input);
    CdcacResult solveLevel(int k, SamplePoint& prefix, const CdcacInput& input);
    CdcacResult checkFullSample(const SamplePoint& sample, const CdcacInput& input);

    Cell buildLeafConflictCell(const CdcacConstraint& c, const SamplePoint& sample, VarId var);

    // P2b: shallow generalization only.
    // Uses current-level constraint roots and full child reasons.
    // Does not perform projection-driven parent generalization.
    // Guards are recorded for future certificate use only.
    BuildCellResult buildConflictCell(
        int k,
        const RealAlg& sample,
        CdcacResult& childRes,
        const CdcacInput& input,
        const RootSet& roots
    );

    bool relationHolds(Sign s, Relation rel) const;

    std::optional<RootSet> mergeRoots(const std::vector<RootSet>& rootSets);

    // Build the (sample-independent) Collins projection closure for this
    // solve's active constraints; sets unsatTrustworthy_ false if incomplete.
    void buildClosure(const CdcacInput& input);

private:
    PolynomialKernel* kernel_;
    AlgebraBackend* algebra_;
    std::unique_ptr<ProjectionPolicy> policy_;  // V4: configurable projection policy

    // Proof-carrying projection state (rebuilt per solve()).
    ProjectionClosure closure_;
    std::vector<std::vector<PolyId>> levelPolyIds_;  // closure polys per level, as PolyId
    // True iff every UNSAT-relevant projection step this solve was complete; a
    // generalized-UNSAT exit is downgraded to Unknown when false — the binding
    // "no UNSAT without a complete projection-certified covering".
    bool unsatTrustworthy_ = true;
};

} // namespace nlcolver
