#pragma once

#include "theory/arith/nra/core/CdcacTypes.h"
#include "theory/arith/nra/core/CdcacConstraint.h"
#include "theory/arith/nra/backend/AlgebraBackend.h"
#include "theory/arith/nra/engine/CoveringManager.h"
#include "theory/arith/nra/engine/ReasonManager.h"
#include "theory/arith/nra/projection/ProjectionPolicy.h"
#include "theory/arith/nra/projection/ProjectionClosure.h"
#include "theory/arith/nra/projection/LazardProjectionClosure.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include <vector>
#include <memory>

namespace zolver {

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

    // Projection mode for the lazily-created default policy. Set from
    // ZOLVER_NRA_PROJECTION in the constructor (lazard => LazardStyle; otherwise
    // CollinsConservative). Ignored if setProjectionPolicy() installs a policy.
    ProjectionPolicyKind projectionKind_ = ProjectionPolicyKind::CollinsConservative;

    // Proof-carrying projection state (rebuilt per solve()).
    ProjectionClosure closure_;
    // Lazard projection closure — used in place of closure_ when projectionKind_
    // == LazardStyle (ZOLVER_NRA_PROJECTION=lazard). Whole-problem, built once
    // per solve(); drives the SAME root-isolation path. Incomplete ⇒ no UNSAT.
    LazardProjectionClosure lazardClosure_;
    std::vector<std::vector<PolyId>> levelPolyIds_;  // closure polys per level, as PolyId
    // True iff every UNSAT-relevant projection step this solve was complete; a
    // generalized-UNSAT exit is downgraded to Unknown when false — the binding
    // "no UNSAT without a complete projection-certified covering".
    bool unsatTrustworthy_ = true;

    // Opt-in (ZOLVER_NRA_LAZARD_LIFT): try Lazard tower root isolation for the
    // genuine-tower lift case (>=2 algebraic prefix coords) that ViaNorm punts
    // on. Default off; only adds certified isolations, never changes the Collins
    // path. Read once in the constructor.
    bool lazardLiftEnabled_ = false;

    // Opt-in soundness FLOOR (ZOLVER_NRA_UNSAT_CERT, intended default-ON once the
    // precise verifier lands). INTERIM CONSERVATIVE form: the CDCAC covering can
    // silently drop a satisfiable region (meti-tarski sqrt false-UNSAT) via a
    // subtle close-root / bilinear-section defect not yet pinned to a cheap
    // positive check, so every CDCAC covering-UNSAT is downgraded to Unknown
    // rather than risk a wrong UNSAT (sound-now at a measured completeness cost).
    // The recursive per-cell sign-invariance + tiling verifier will replace this
    // with a precise certify-or-downgrade. Read once in the constructor.
    bool unsatCertEnabled_ = false;

    // PRECISE verifier state (reset per solve). Set true when a level's covering
    // cannot be positively certified sound — currently: the libpoly-isolated
    // boundary set `allRoots` is INCOMPLETE vs an independent exact Sturm-over-ℚ
    // count of the level's closure polynomials (a missed/merged root ⇒ a cell is
    // not sign-invariant ⇒ a satisfiable region can be dropped), or the prefix is
    // algebraic (not yet certifiable by the ℚ-Sturm oracle). A certified covering
    // (no uncertifiable level) keeps emitting UNSAT; otherwise → Unknown.
    bool coveringUncertifiable_ = false;

    // Independent exact-Sturm sign-invariance check for level k's covering: true
    // iff `allRoots` captured every real root of the level's closure polys
    // (rational prefix only; algebraic prefix ⇒ false = cannot certify).
    bool certifyLevelSignInvariance(int k, const SamplePoint& prefix,
                                    const CdcacInput& input, const RootSet& allRoots);
};

} // namespace zolver
