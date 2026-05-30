#pragma once

#include "theory/arith/ArithSolverBase.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include "theory/arith/poly/PolynomialConverter.h"
#include "theory/arith/nra/core/CdcacSolver.h"
#include "theory/combination/SharedTermRegistry.h"
#include "theory/core/ActiveLiteralSet.h"
#include "theory/core/TheoryAtomTypes.h"
#include <memory>
#include <optional>
#include <unordered_map>
#include <vector>
#include <gmpxx.h>

namespace xolver {

class NraLinearizationAdapter;
class TheoryAtomRegistry;
class CdcacCore;       // XOLVER_NRA_PREELIM: lazily-built reduced-CDCAC core
class LibpolyBackend;  // XOLVER_NRA_PREELIM: algebra backend for the pre-elim core

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
    // hooks rather than using the shared state_.trail. check() is the
    // base default (runReasonerPipeline over the two stages below).
    void assertLit(const TheoryAtomRecord& atom, bool value, int level, SatLit reason) override;

    void setCoreIr(const CoreIr* ir) { coreIr_ = ir; }
    void setSharedTermRegistry(const SharedTermRegistry* reg) { sharedTermRegistry_ = reg; }
    // XOLVER_NRA_LINEARIZE: registry needed to mint mirror/cut literals for the
    // LRA sibling. Mirrors NiaSolver::setRegistry; builds the linearization
    // adapter lazily.
    void setRegistry(TheoryAtomRegistry* reg);
    // XOLVER_NRA_LINEARIZE: pointer to the LRA sibling registered alongside NRA
    // in the same (single-theory) TheoryManager. The linearize-probe stage reads
    // its candidate relaxation model (getModel()) to attempt a validated SAT.
    // Harmless when the flag is OFF (only the gated stage reads it).
    void setLinearSibling(TheorySolver* s) { linearSibling_ = s; }

    bool supportsCombination() const override { return true; }

    TheoryCheckResult assertInterfaceEquality(
        SharedTermId a, SharedTermId b, SatLit reason, int level) override;
    TheoryCheckResult assertInterfaceDisequality(
        SharedTermId a, SharedTermId b, SatLit reason, int level) override;

    std::vector<SharedEqualityPropagation>
    getDeducedSharedEqualities() override;

    std::optional<TheoryModel> getModel() const override;

protected:
    void onPush() override;
    void onPop(uint32_t n) override;
    void onBacktrack(int targetLevel) override;
    void onReset() override;

private:
    // Reasoner pipeline stages (Phase 2). nullopt = continue.
    std::optional<TheoryCheckResult> stagePresolve(TheoryLemmaStorage& lemmaDb, TheoryEffort effort);
    // XOLVER_NRA_SIGN_REFUTE (default OFF): positive-orthant sign-definiteness
    // refuter. From single-variable bounds, fix each var's sign; if some
    // constraint g rel 0 is sign-definite over that orthant and contradicts rel
    // (e.g. a sum of strictly-positive monomials = 0), emit the UNSAT conflict.
    // O(#monomials); unconditionally sound (refutes only the provably impossible)
    // — the cheap closer for the Sturm-MBO family that CAD/CAC time out on.
    std::optional<TheoryCheckResult> stageSignRefute(TheoryLemmaStorage& lemmaDb, TheoryEffort effort);
    // XOLVER_NRA_LINEARIZE incremental-linearization SAT loop (default OFF):
    // read the LRA sibling's relaxation model, exact-validate every original
    // constraint (consistent()/SAT if all hold), else emit model-tangent cuts
    // and return one as a Lemma to defer CDCAC + re-solve. nullopt when the flag
    // is OFF or the refinement budget is exhausted (fall through to CDCAC).
    std::optional<TheoryCheckResult> stageLinearizeProbe(TheoryLemmaStorage& lemmaDb, TheoryEffort effort);
    // XOLVER_NRA_PREELIM (default OFF): affine-equality pre-elimination. Collect
    // `v = (linear expr)` substitutions from the presolve fixpoint, substitute the
    // eliminated vars out of every constraint poly, and run a reduced CDCAC over the
    // remaining variables (CAD is doubly-exponential in #vars). UNSAT unions every
    // eliminated var's defining-equality reason; SAT reconstructs the eliminated vars
    // and validates over the ORIGINAL constraints (invariant 1). nullopt at the gate
    // when the flag is OFF (default path byte-identical).
    std::optional<TheoryCheckResult> stageNraPreElim(TheoryLemmaStorage& lemmaDb, TheoryEffort effort);
    // XOLVER_NRA_SUBTROPICAL (default OFF): subtropical SAT-fast-path. A cheap,
    // incomplete witness search "at infinity" (substitute x_i = s_i*B^{a_i}); on
    // a found candidate, materialize over increasing bases and EXACT-validate
    // every active original constraint via the kernel sign (invariant 1) — SAT
    // only on a validated model, else nullopt (fall through to CDCAC). Full
    // effort only. nullopt immediately when the flag is OFF.
    std::optional<TheoryCheckResult> stageSubtropical(TheoryLemmaStorage& lemmaDb, TheoryEffort effort);
    // XOLVER_NRA_CAC (A/B control for the Collins-vs-CAC differential): run the
    // conflict-driven single-cell CAC engine (the "real" CDCAC) as the primary
    // NRA decision at Full effort, BEFORE the Collins buildClosure. SAT (a
    // rational witness the engine already validated) ⇒ consistent() + model stash;
    // UNSAT (gap-free covering) ⇒ a theory conflict over the active reasons;
    // Unknown / algebraic SAT model ⇒ nullopt (fall through to Collins). The flag
    // gates promotion; whether CAC becomes the default is decided by the
    // differential, not pinned here.
    std::optional<TheoryCheckResult> stageCac(TheoryLemmaStorage& lemmaDb, TheoryEffort effort);
    std::optional<TheoryCheckResult> stageCdcac(TheoryLemmaStorage& lemmaDb, TheoryEffort effort);

    struct NraTrailEntry {
        int level;
        size_t activeSizeBefore;
    };

    std::unique_ptr<PolynomialKernel> kernel_;
    std::unique_ptr<PolynomialConverter> converter_;
    CdcacSolver engine_;

    std::vector<SatLit> activeLits_;
    std::vector<NraTrailEntry> trail_;
    ActiveLiteralSet activeSet_;

    // Active polynomial constraints (poly - rhs) rel 0, aligned 1:1 with
    // activeLits_, for the theory-check presolve fixpoint.  NullPoly entries
    // are non-polynomial placeholders (kept aligned, skipped by presolve).
    struct PresolveCstr { PolyId poly; Relation rel; SatLit reason; };
    std::vector<PresolveCstr> presolveConstraints_;

    // XOLVER_NRA_LINEARIZE: full active-assignment records captured at
    // assertLit, aligned 1:1 with activeLits_/presolveConstraints_, so the
    // cut-feeder can mirror linear bounds to the LRA sibling. Held only to feed
    // NraLinearizationAdapter::mirrorActiveLinearBounds (needs lit+atom+value).
    struct ActiveRecord { SatLit lit; TheoryAtomRecord atom; bool value; };
    std::vector<ActiveRecord> activeRecords_;

    const CoreIr* coreIr_ = nullptr;
    const SharedTermRegistry* sharedTermRegistry_ = nullptr;

    // XOLVER_NRA_LINEARIZE: registry + linearization adapter (mirror lemmas +
    // McCormick/square cut lemmas). Built lazily by setRegistry.
    TheoryAtomRegistry* registry_ = nullptr;
    std::unique_ptr<NraLinearizationAdapter> linAdapter_;
    // XOLVER_NRA_LINEARIZE: LRA sibling (raw, non-owning) whose relaxation model
    // we exact-validate; refinement-round counter for the incremental loop
    // (reset on backtrack/reset so each search restarts the budget).
    TheorySolver* linearSibling_ = nullptr;
    int linRefineRound_ = 0;

    struct InterfaceEq {
        SharedTermId a;
        SharedTermId b;
        SatLit reason;
        int level;
    };
    std::vector<InterfaceEq> interfaceEqualities_;
    std::vector<InterfaceEq> interfaceDisequalities_;

    // #43: dedup pairs already emitted by getDeducedSharedEqualities under the
    // CURRENT satFastModel_, so the combination loop terminates. Cleared every
    // time satFastModel_ is reset (assignment change ⇒ deductions stale).
    std::set<std::pair<SharedTermId, SharedTermId>> deducedSharedEqEmitted_;

    // V5: scope stack for push/pop
    std::vector<size_t> scopeStack_;

    // XOLVER_NRA_PREELIM: gate + lazily-built reduced-CDCAC core/backend. The
    // core is rebuilt per solve (stateless across calls except the libpoly var
    // table), so it can persist across theory-checks; reset in onReset.
    bool enablePreElim_ = false;
    std::unique_ptr<LibpolyBackend> preElimAlgebra_;
    std::unique_ptr<CdcacCore> preElimCore_;

    // Subtropical SAT-fast-path: promoted default-ON.
    bool enableSubtropical_ = true;
    // The validated subtropical/CAC witness for the CURRENT full assignment, if a
    // SAT-fast-path fired. getModel() prefers it over the (bypassed) CDCAC engine
    // sample. Invalidated by any assignment change (assertLit/backtrack/pop/reset).
    std::optional<std::unordered_map<VarId, mpq_class>> satFastModel_;

    // CAC (CDCAC) engine: promoted default-ON. Lazily-built libpoly backend.
    bool enableCac_ = true;
    std::unique_ptr<LibpolyBackend> cacBackend_;

    // Sign-definiteness refuter: promoted default-ON.
    bool enableSignRefute_ = true;
};

} // namespace xolver
