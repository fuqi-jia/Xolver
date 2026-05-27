#pragma once

#include "theory/arith/ArithSolverBase.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include "theory/arith/poly/PolynomialConverter.h"
#include "theory/arith/nra/core/CdcacSolver.h"
#include "theory/combination/SharedTermRegistry.h"
#include "theory/core/ActiveLiteralSet.h"
#include "theory/core/TheoryAtomTypes.h"
#include <memory>
#include <vector>

namespace zolver {

class NraLinearizationAdapter;
class TheoryAtomRegistry;

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
    // ZOLVER_NRA_LINEARIZE: registry needed to mint mirror/cut literals for the
    // LRA sibling. Mirrors NiaSolver::setRegistry; builds the linearization
    // adapter lazily.
    void setRegistry(TheoryAtomRegistry* reg);
    // ZOLVER_NRA_LINEARIZE: pointer to the LRA sibling registered alongside NRA
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
    // ZOLVER_NRA_LINEARIZE incremental-linearization SAT loop (default OFF):
    // read the LRA sibling's relaxation model, exact-validate every original
    // constraint (consistent()/SAT if all hold), else emit model-tangent cuts
    // and return one as a Lemma to defer CDCAC + re-solve. nullopt when the flag
    // is OFF or the refinement budget is exhausted (fall through to CDCAC).
    std::optional<TheoryCheckResult> stageLinearizeProbe(TheoryLemmaStorage& lemmaDb, TheoryEffort effort);
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

    // ZOLVER_NRA_LINEARIZE: full active-assignment records captured at
    // assertLit, aligned 1:1 with activeLits_/presolveConstraints_, so the
    // cut-feeder can mirror linear bounds to the LRA sibling. Held only to feed
    // NraLinearizationAdapter::mirrorActiveLinearBounds (needs lit+atom+value).
    struct ActiveRecord { SatLit lit; TheoryAtomRecord atom; bool value; };
    std::vector<ActiveRecord> activeRecords_;

    const CoreIr* coreIr_ = nullptr;
    const SharedTermRegistry* sharedTermRegistry_ = nullptr;

    // ZOLVER_NRA_LINEARIZE: registry + linearization adapter (mirror lemmas +
    // McCormick/square cut lemmas). Built lazily by setRegistry.
    TheoryAtomRegistry* registry_ = nullptr;
    std::unique_ptr<NraLinearizationAdapter> linAdapter_;
    // ZOLVER_NRA_LINEARIZE: LRA sibling (raw, non-owning) whose relaxation model
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

    // V5: scope stack for push/pop
    std::vector<size_t> scopeStack_;
};

} // namespace zolver
