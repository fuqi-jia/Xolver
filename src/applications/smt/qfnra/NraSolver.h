#pragma once

#include "search/arith/ArithSolverBase.h"
#include "algebra/poly/PolynomialKernel.h"
#include "algebra/poly/PolynomialConverter.h"
#include "search/nra/core/CdcacSolver.h"
#include "search/combination/SharedTermRegistry.h"
#include "contracts/ActiveLiteralSet.h"
#include "contracts/TheoryAtomTypes.h"
#include "base/RealValue.h"   // #55 Phase B: algebraic SAT model channel
#include <memory>
#include <optional>
#include <unordered_map>
#include <vector>
#include <gmpxx.h>

namespace xolver {

class TheoryAtomRegistry;
class LibpolyBackend;  // Algebra backend for cylindrical coverings.

/**
 * NRA (Nonlinear Real Arithmetic) theory solver.
 *
 * Facade that delegates polynomial constraint checking to the
 * underlying CDCAC engine (CdcacSolver). Future phases may support
 * multiple NRA backends (e.g., local search, MCSAT) selected
 * dynamically.
 */
class NraSolver : public ArithSolverBase {
public:
    explicit NraSolver(std::unique_ptr<PolynomialKernel> kernel);
    ~NraSolver() override;  // out-of-line: NraLinearizationAdapter is incomplete here

    TheoryId id() const override { return TheoryId::NRA; }

    // Expose kernel so Atomizer can share the same instance.
    PolynomialKernel* kernel() const { return kernel_.get(); }

    // NRA is a facade over CdcacSolver with its own active-literal
    // tracking (activeLits_/trail_/activeSet_), so it overrides
    // assertLit and routes push/pop/backtrack/reset through the base
    // hooks rather than using the shared state_.trail.
    void assertLit(const TheoryAtomRecord& atom, bool value, int level, SatLit reason) override;
    // Check routing invariants before entering the scheduled reasoners.
    TheoryCheckResult check(TheoryLemmaStorage& lemmaDb, TheoryEffort effort) override;

    // setNativeTerms / setSharedTermRegistry now live in ArithSolverBase
    // (hoisted 2026-06-04 with getVarNameForSharedTerm).
    bool supportsCombination() const override { return true; }

    TheoryCheckResult assertInterfaceEquality(
        SharedTermId a, SharedTermId b, SatLit reason, int level) override;
    TheoryCheckResult assertInterfaceDisequality(
        SharedTermId a, SharedTermId b, SatLit reason, int level) override;

    std::optional<TheoryModel> getModel() const override;

protected:
    void onPush() override;
    void onPop(uint32_t n) override;
    void onBacktrack(int targetLevel) override;
    void onReset() override;

private:
    void invalidateModel();
    bool validateRationalCandidate(std::unordered_map<VarId, mpq_class>& candidate) const;
    std::optional<TheoryCheckResult> stageLocalSearch(TheoryLemmaStorage&, TheoryEffort);
    // Reasoner pipeline stages (Phase 2). nullopt = continue.
    std::optional<TheoryCheckResult> stagePresolve(TheoryLemmaStorage& lemmaDb, TheoryEffort effort);
    // Refute the affine relaxation over independent monomial values before
    // algebraic search. A feasible relaxation never establishes NRA SAT.
    std::optional<TheoryCheckResult> stageLinearRelaxation(TheoryLemmaStorage& lemmaDb, TheoryEffort effort);
    // Positive-orthant sign-definiteness
    // refuter. From single-variable bounds, fix each var's sign; if some
    // constraint g rel 0 is sign-definite over that orthant and contradicts rel
    // (e.g. a sum of strictly-positive monomials = 0), emit the UNSAT conflict.
    // O(#monomials); unconditionally sound (refutes only the provably impossible)
    // — the cheap closer for the Sturm-MBO family that CAD/CAC time out on.
    std::optional<TheoryCheckResult> stageSignRefute(TheoryLemmaStorage& lemmaDb, TheoryEffort effort);
    // Step 2.1: GLOBAL box-consistency refutation (early stage before the covering).
    // Decides bound-contradiction families (hong) in ~ms; sound by over-approximation.
    std::optional<TheoryCheckResult> stageBoxRefute(TheoryLemmaStorage& lemmaDb, TheoryEffort effort);
    // Subtropical candidate search. A cheap,
    // incomplete witness search "at infinity" (substitute x_i = s_i*B^{a_i}); on
    // a found candidate, materialize over increasing bases and EXACT-validate
    // every active original constraint via the kernel sign (invariant 1) — SAT
    // only on a validated model, else nullopt (fall through to CDCAC). Full
    // effort only.
    std::optional<TheoryCheckResult> stageSubtropical(TheoryLemmaStorage& lemmaDb, TheoryEffort effort);
    // Equality-cascade SAT solver for
    // mgc-class systems (assign high-degree generators → residual equalities go
    // linear → derive the rest → validate exactly via the kernel sign). Returns
    // consistent() on a validated model (stashed in satFastModel_), nullopt
    // otherwise. Pure-NRA only (skips combination/N-O mode).
    std::optional<TheoryCheckResult> stageCascade(TheoryLemmaStorage& lemmaDb, TheoryEffort effort);
    // Algebraic square-cascade: constructs + exact-validates a Q(sqrt c) model for
    // square-defined systems (e.g. Geogebra IsoRightTriangle) that the rational
    // eq-cascade and the Lazard delineation both miss. Emits satCacAlgModel_.
    std::optional<TheoryCheckResult> stageSquareCascade(TheoryLemmaStorage& lemmaDb, TheoryEffort effort);
    // Conflict-driven cylindrical covering before the Collins backend.
    // Validated candidates supply models; infeasible coverings supply
    // conflicts with active reasons. Inconclusive results fall through.
    std::optional<TheoryCheckResult> stageCac(TheoryLemmaStorage& lemmaDb, TheoryEffort effort);
    std::optional<TheoryCheckResult> stageCdcac(TheoryLemmaStorage& lemmaDb, TheoryEffort effort);

    struct NraTrailEntry {
        int level;
        size_t activeSizeBefore;
    };

    std::unique_ptr<PolynomialKernel> kernel_;
    std::unique_ptr<PolynomialConverter> converter_;
    CdcacSolver engine_;
    // libpoly hardening: decline the CDCAC path (→ unknown, sound) on inputs above
    // these thresholds, preventing libpoly blowup/OOM on pathological systems.
    // 0 = disabled (default ⇒ no corpus impact); tuned on the benchmark set.
    int cdcacMaxVars_ = 0;   // XOLVER_NRA_CDCAC_MAX_VARS
    int cdcacMaxDeg_ = 0;    // XOLVER_NRA_CDCAC_MAX_DEGREE

    std::vector<SatLit> activeLits_;
    std::vector<NraTrailEntry> trail_;
    ActiveLiteralSet activeSet_;

    // Active polynomial constraints (poly - rhs) rel 0, aligned 1:1 with
    // activeLits_, for the theory-check presolve fixpoint.  NullPoly entries
    // are non-polynomial placeholders (kept aligned, skipped by presolve).
    struct PresolveCstr { PolyId poly; Relation rel; SatLit reason; };
    std::vector<PresolveCstr> presolveConstraints_;

    struct InterfaceEq {
        SharedTermId a;
        SharedTermId b;
        SatLit reason;
        int level;
        PolyId poly;  // converted once at assertion, in (poly rel 0) form
    };
    std::vector<InterfaceEq> interfaceEqualities_;
    std::vector<InterfaceEq> interfaceDisequalities_;

    struct ScopeSnapshot {
        size_t activeSize;
        size_t trailSize;
        size_t equalitySize;
        size_t disequalitySize;
    };
    std::vector<ScopeSnapshot> scopeStack_;

    // The validated subtropical/CAC witness for the CURRENT full assignment, if a
    // SAT-fast-path fired. getModel() prefers it over the (bypassed) CDCAC engine
    // sample. Invalidated by any assignment change (assertLit/backtrack/pop/reset).
    std::optional<std::unordered_map<VarId, mpq_class>> satFastModel_;

    // #55 Phase B: CAC SAT model with algebraic values (set when
    // XOLVER_NRA_CAC_SAT_ALGEBRAIC is ON and the CAC SAT sample contains
    // at least one RealAlg value). Surface via getModel() through the
    // RealValue-typed numericAssignments channel. Cleared at every
    // satFastModel_.reset() site.
    std::optional<std::vector<std::pair<VarId, RealValue>>> satCacAlgModel_;

    // Candidate-model search shares a per-query time allocation. Repeating the
    // same constraint set does not restart search; a changed set may use the
    // remaining time. Keys compare complete (poly, relation) vectors, not hashes.
    long lsSpentMs_ = 0;
    std::vector<std::pair<PolyId, Relation>> lsLastConstraints_;
    size_t hybStatsLastDumpedSize_ = static_cast<size_t>(-1);
    // Cached witnesses survive assertion changes only as untrusted candidates;
    // reuse validates all ordinary and interface constraints exactly.
    std::optional<std::unordered_map<VarId, mpq_class>> lsCachedCandidate_;

    // Lazily-built libpoly backend for cylindrical coverings.
    std::unique_ptr<LibpolyBackend> cacBackend_;

    // NRA-MGC-PROFILE: env-gated per-stage timing accounting (XOLVER_NRA_STAGE_TIMING).
    mutable std::unordered_map<std::string, uint64_t> stageTimingUs_;
    mutable std::unordered_map<std::string, uint64_t> stageTimingCalls_;
};

} // namespace xolver
