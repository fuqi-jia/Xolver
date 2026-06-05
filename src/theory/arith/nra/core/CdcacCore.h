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
#include "theory/arith/poly/RationalPolynomial.h"
#include <vector>
#include <memory>
#include <optional>
#include <chrono>

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

    // Build the leaf-style UNSAT result for a set of violated constraints (each
    // paired with its DEFINITE sign at the current point). The cell is FullLine
    // with a COMPLETE LazardCellCertificate (every listed sign was definite).
    // Shared by checkFullSample (the full-sample leaf) and solveLevel's
    // forward-prune (a constraint already determined+violated at an internal
    // level). `violated` indexes input.constraints.
    CdcacResult makeLeafConflictResult(const std::vector<std::pair<size_t, Sign>>& violated,
                                       const CdcacInput& input);

    // Per-constraint variable sets (VarId), built once per input for solveLevel's
    // forward-prune "is this constraint fully determined by the prefix?" test.
    // Rebuilt when the constraint count changes; cleared in resetPerSolveState.
    std::vector<std::vector<VarId>> constraintVarsCache_;
    const std::vector<VarId>& constraintVars(size_t ci, const CdcacInput& input);

    // nlsat-engine STEP A (XOLVER_NRA_CAC_SAT_FIRST): SAT-only model-constructing
    // search, run ONCE before the eager buildClosure. Delineates each var's cells
    // LAZILY from the raw constraints (specializeToUnivariate + isolateRealRoots —
    // single-cell, no closure), samples one RATIONAL per cell, forward-checks each
    // partial assignment, and recurses; the leaf is checkFullSample (exact signAt
    // validation). Returns Sat ONLY on a kernel-validated full sample → sound by
    // construction; NEVER returns Unsat. A coefficient-bit cap guards every libpoly
    // call so high-degree/huge-coeff inputs are skipped, not crashed. Budget-bounded;
    // Unknown on exhaustion → falls through to the projection engine unchanged.
    CdcacResult trySatSampleFirst(int k, SamplePoint& prefix,
                                  const CdcacInput& input, long& budget);
    std::vector<mpq_class> satSampleCandidates(int k, const SamplePoint& prefix,
                                               const CdcacInput& input);

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
    //   XOLVER_NRA_PROJECTION=collins => pure Collins.
    // Promoted default-ON (broad differential 0-unsound).
    bool hybridEnabled_ = true;

    // nlsat-engine STEP A gate + state. Default-OFF until the broad gate lands;
    // sound by construction (SAT-only, checkFullSample-validated). One-shot per
    // CdcacCore lifetime (= per SMT-solve in non-incremental) via satFirstTried_.
    bool satFirstEnabled_ = false;
    // Node-search backstop (raised from 20000: matrix-class SAT models need ~300k
    // nodes to reach — the old cap aborted the search 15x too early). The REAL
    // bound is the wall-clock cap satFirstMs_ below; this just caps a pathological
    // node count if the clock check is somehow never hit.
    long satFirstBudget_ = 2000000;
    // Wall-clock cap (ms) on the whole SAT-first search. Bounds the model-search
    // so it can't starve the downstream complete engine on a no-model input
    // (the OSF-latency lesson): on expiry the search bails → falls through to
    // projection, byte-identical to never having run. Env XOLVER_NRA_CAC_SAT_FIRST_MS.
    // 10s gives the matrix-class SAT cluster comfortable margin (recovers in ~7.6s)
    // while the full nra/nira regression stays 151/151 + 30/30 0-unsound with the
    // flag ON (cap can't starve projection on the curated cases).
    long satFirstMs_ = 10000;
    std::chrono::steady_clock::time_point satFirstT0_;  // search start (set in solve())
    bool satFirstTried_ = false;
    // Increment 4 (XOLVER_NRA_CAC_SAT_FIRST_ALG, default-OFF): ALGEBRAIC-model
    // SAT-first. The rational-only path (above) samples rationals and leaf-validates
    // via exactSignAt (pure-mpq, crash-free) — so it CANNOT find a model with an
    // algebraic coordinate (e.g. Geogebra geometry: v9=√2). This path offers the
    // actual ALGEBRAIC roots (RealAlg, not their rational midpoints) as candidates
    // and evaluates the leaf + forward-check over the algebraic sample via
    // algebra_->signAt (libpoly algebraic sign). Soundness-SAFE (Sat only on a full
    // signAt-validated point; signAt==Unknown is treated as inconclusive and never
    // concludes). Crash-capped: runs ONLY when every constraint's total degree is
    // ≤ satFirstAlgDegCap_ (the libpoly algebraic-sign path OOM-crashes on high
    // degree — the matrix class — so we restrict to the low-degree algebraic regime,
    // Geogebra ~deg-3). Implies satFirstEnabled_.
    bool satFirstAlgEnabled_ = false;
    long satFirstAlgDegCap_ = 6;
    CdcacResult trySatSampleFirstAlg(int k, SamplePoint& prefix,
                                     const CdcacInput& input, long& budget);
    std::vector<RealAlg> satSampleCandidatesAlg(int k, const SamplePoint& prefix,
                                                const CdcacInput& input);
    // M1+M2 (XOLVER_NRA_CAC_SAT_FIRST_LOOKAHEAD, default-OFF): forward infeasibility
    // propagation for the rational SAT-first. After assigning var k, check whether
    // any UNASSIGNED variable already has an EMPTY feasible set — i.e. its
    // constraints that are now univariate-in-it (all their other vars assigned)
    // admit no satisfying cell. If so the current prefix cannot be completed, so
    // prune it NOW (an EARLY/shallow conflict) instead of descending to that
    // variable's level and failing late. Soundness-SAFE for SAT: only prunes
    // prefixes with a provably-infeasible future variable (cell-rep sampling covers
    // every sign-invariant cell, so a feasible cell is never missed). The genuine
    // MCSAT lever — see docs/nra-nlsat-diagnosis.md "MCSAT BUILD SPEC" M1/M2.
    bool satFirstLookaheadEnabled_ = false;
    // M2 (true ICP): is the whole subtree under the current rational prefix `m`
    // provably infeasible by box-consistency propagation? Builds an extended-interval
    // box (±∞) for every UNASSIGNED var, then runs an HC4-revise fixpoint: (A) natural
    // interval extension of each constraint poly over the box — if its range excludes
    // every value consistent with the relation, the subtree is infeasible; (B) degree-1
    // contraction (A·v+B rel 0) tightens each unassigned var's box. Sound by
    // over-approximation: boxes always CONTAIN the feasible projection, so it can prove
    // infeasibility but NEVER over-prune a real model (no algebraic-boundary risk).
    // See docs/nra-nlsat-diagnosis.md "MCSAT BUILD SPEC" M1/M2.
    bool subtreeBoxInfeasible(const std::unordered_map<VarId, mpq_class>& m,
                              const CdcacInput& input);
    // Per-constraint "safe to delineate via libpoly" flags (coeff-bit cap),
    // precomputed once per sample-first search so high-degree/huge-coeff polys are
    // skipped (not crashed). Indexed parallel to input.constraints.
    std::vector<bool> satSafe_;
    // Cached EXACT rational polynomial per constraint (parallel to satSafe_),
    // built once in the satSafe_ pass. The leaf/forward-check evaluate signs via
    // pure-mpq Horner over these (exactSign) — NEVER libpoly coefficient_sgn,
    // whose rational_interval_pow OOM-SIGSEGVs raising a large rational sample to
    // a power (the matrix-1-all crash). Present for every constraint whenever the
    // all-safe gate lets the search run.
    std::vector<std::optional<RationalPolynomial>> satRp_;
    // Increment 3 (XOLVER_NRA_CAC_NLSAT, default-OFF): LAZY conflict-driven
    // projection learning. When a variable's feasible set is empty (no sampled
    // candidate survives the forward-check), project ONLY the conflict core
    // (eliminating that var) via a Collins policy and add each result as a DERIVED
    // feasibility cut that prunes the re-search — z3-nlsat's advantage over the
    // eager buildClosure projection (which projects everything up front and
    // explodes on the matrix cluster). Soundness-SAFE: SAT-first never emits Unsat;
    // a wrong cut only over-prunes (misses a model → falls through), never a wrong
    // verdict. Reset per solve. NOT a budget — the search pruning is algorithmic.
    bool satNlsatEnabled_ = false;
    // A learned infeasible CELL over the lower (already-assigned) variables: the
    // CONJUNCTION of sign conditions on the projection polynomials that, when ALL
    // hold, proved the just-conflicted variable infeasible. Pruning the INTERSECTION
    // (this exact sign-cell) — not each half-space independently — is what makes the
    // generalization sound-for-completeness: it excludes only the region the
    // projection certifies infeasible, never the SAT region. (Storing per-poly cuts
    // and pruning on ANY-violation excluded the UNION of half-spaces ⇒ over-pruned
    // the model — the iter-18 net-negative.)
    struct SatSignCond { RationalPolynomial poly; int sign; };  // sgn(poly) == sign over lower vars
    struct SatDeadCell { int level; std::vector<SatSignCond> conds; };  // conds ALL hold ⇒ var[level] infeasible
    std::vector<SatDeadCell> satDerivedCells_;
    std::unique_ptr<ProjectionPolicy> satExplainPolicy_;
    void projectConflictCore(int k, VarId var, const SamplePoint& prefix,
                             const CdcacInput& input);
    // True if the lower-var assignment `m` matches ALL sign conditions of some
    // learned dead cell at this `level` ⇒ var[level] is infeasible here, so prune
    // the whole subtree without sampling it. (Intersection match, not union.)
    bool prefixInLearnedDeadCell(int level, const std::unordered_map<VarId, mpq_class>& m) const;
    // Magnitude bound (bits) on sampled cell representatives. SAT-first samples
    // the SIMPLEST rational in each feasible cell (smallest-denominator dyadic) and
    // discards any whose numerator/denominator exceeds this — an ADDITIVE search
    // restriction (real models have small coords; the complete projection engine
    // still runs on fall-through), which also keeps every downstream
    // specialization/evaluation bounded. Tunable via XOLVER_NRA_CAC_SAT_FIRST_MAX_BITS.
    long satSampleMaxBits_ = 64;

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
