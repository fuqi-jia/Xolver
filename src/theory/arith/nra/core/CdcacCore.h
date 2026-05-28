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

namespace xolver {

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
        const RootSet& roots,
        bool levelBoundaryComplete,
        std::optional<FullLineReason> fullLineReason = std::nullopt
    );

    // FAIL-SAFE per-cell gate helper. Populate a cell's LazardCellCertificate
    // from this level's boundary completeness + the child covering's per-cell
    // completeness. Sets every *Complete flag true ONLY when provably so.
    LazardCellCertificate makeLazardCellCert(
        bool levelBoundaryComplete,
        bool levelRootIsolationComplete,
        const CdcacResult& childRes,
        std::optional<FullLineReason> fullLineReason) const;

    // True iff EVERY cell in a covering certificate carries a complete Lazard
    // cell certificate (recursively gated through childCoverCert).
    static bool coveringCellsAllComplete(const CoveringCertificate& cert);

    bool relationHolds(Sign s, Relation rel) const;

    std::optional<RootSet> mergeRoots(const std::vector<RootSet>& rootSets);

    // Build the (sample-independent) Collins projection closure for this
    // solve's active constraints; sets unsatTrustworthy_ false if incomplete.
    void buildClosure(const CdcacInput& input);

    // Run a single CDCAC pass (buildClosure + solveLevel) with the projection
    // configuration currently set on this core (projectionKind_/lazardLiftEnabled_).
    // Used by the hybrid driver to run Collins then (on Unknown) Lazard. Carries
    // the existing XOLVER_NRA_UNSAT_CERT soundness floor.
    CdcacResult solvePass(const CdcacInput& input);

    // Reset all per-solve scratch state so a second pass over the SAME input
    // starts clean (closures, level polys, the lazily-created policy, and the
    // completeness/trust flags). Does NOT touch the configured projection mode.
    void resetPerSolveState();

private:
    PolynomialKernel* kernel_;
    AlgebraBackend* algebra_;
    std::unique_ptr<ProjectionPolicy> policy_;  // V4: configurable projection policy

    // Projection mode for the lazily-created default policy. Set from
    // XOLVER_NRA_PROJECTION in the constructor (lazard => LazardStyle; otherwise
    // CollinsConservative). Ignored if setProjectionPolicy() installs a policy.
    // In HYBRID mode this is flipped per-pass by solve() (Collins then Lazard).
    ProjectionPolicyKind projectionKind_ = ProjectionPolicyKind::CollinsConservative;

    // FAIL-SAFE HYBRID (DEFAULT): run Collins first, and ONLY if Collins returns
    // Unknown, re-run the SAME input under the Lazard configuration
    // (projectionKind_ = LazardStyle + lazardLiftEnabled_ + the per-cell UNSAT
    // cert gate). Collins's definite verdicts (Sat/Unsat) are ALWAYS authoritative
    // — Lazard never overrides them — so the hybrid is strictly >= pure-Collins by
    // construction (it can only recover a Collins-Unknown to a Lazard-certified
    // Sat/Unsat). The Lazard pass's Sat is full-model-validated upstream and its
    // Unsat is the committed cert-gated path (incomplete => Unknown).
    // DEFAULT-OFF at integration (master): the broad >=300-case QF_NRA z3
    // differential — the hard promotion gate for a default-path NRA change — has
    // NOT run yet, and the submission is soundness-primary (one false-UNSAT sinks
    // the division). Default path is therefore pure Collins, byte-identical to the
    // pre-Lazard baseline. Opt in / out, read once in the constructor:
    //   XOLVER_NRA_HYBRID=1            => enable hybrid (Collins-first, Lazard on Unknown).
    //   XOLVER_NRA_PROJECTION=lazard   => pure Lazard.
    //   XOLVER_NRA_PROJECTION=collins / XOLVER_NRA_HYBRID=0 / unset => pure Collins.
    // Promote to default-ON only after the broad differential is 0-unsound.
    bool hybridEnabled_ = false;

    // Proof-carrying projection state (rebuilt per solve()).
    ProjectionClosure closure_;
    // Lazard projection closure — used in place of closure_ when projectionKind_
    // == LazardStyle (XOLVER_NRA_PROJECTION=lazard). Whole-problem, built once
    // per solve(); drives the SAME root-isolation path. Incomplete ⇒ no UNSAT.
    LazardProjectionClosure lazardClosure_;
    std::vector<std::vector<PolyId>> levelPolyIds_;  // closure polys per level, as PolyId
    // True iff every UNSAT-relevant projection step this solve was complete; a
    // generalized-UNSAT exit is downgraded to Unknown when false — the binding
    // "no UNSAT without a complete projection-certified covering".
    bool unsatTrustworthy_ = true;

    // Opt-in (XOLVER_NRA_LAZARD_LIFT): try Lazard tower root isolation for the
    // genuine-tower lift case (>=2 algebraic prefix coords) that ViaNorm punts
    // on. Default off; only adds certified isolations, never changes the Collins
    // path. Read once in the constructor.
    bool lazardLiftEnabled_ = false;

    // FAIL-SAFE per-cell UNSAT gate (Lazard mode only). The per-solve
    // `unsatTrustworthy_` flag is over-conservative: it is dropped by ANY
    // incomplete step anywhere in the solve tree (including exploratory branches
    // that never enter the final covering), flooring recoverable UNSATs to
    // Unknown. The per-cell gate trusts a covering's UNSAT if EITHER
    // `unsatTrustworthy_` is true (current behaviour) OR every cell in that
    // covering carries a complete `LazardCellCertificate` (boundary construction
    // for the cell complete AND its recursive child covering complete). This is
    // strictly >= the per-solve gate: it can only turn current-Unknowns into
    // UNSAT, never the reverse, and never weakens the Collins path. Enabled by
    // default in Lazard mode; force-off with XOLVER_NRA_LAZARD_CELL_CERT=0.
    bool lazardCellCertEnabled_ = true;

    // Per-solve: was the Lazard projection closure built to completion? Mirrors
    // the closure-completeness folding in buildClosure(). Fail-safe false.
    bool closureComplete_ = false;

    // Opt-in soundness FLOOR (XOLVER_NRA_UNSAT_CERT, intended default-ON once the
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

} // namespace xolver
