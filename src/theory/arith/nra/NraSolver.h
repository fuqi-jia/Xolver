#pragma once

#include "theory/arith/ArithSolverBase.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include "theory/arith/poly/PolynomialConverter.h"
#include "theory/arith/nra/core/CdcacSolver.h"
#include "theory/combination/SharedTermRegistry.h"
#include "theory/core/ActiveLiteralSet.h"
#include <memory>
#include <vector>

namespace nlcolver {

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

    const CoreIr* coreIr_ = nullptr;
    const SharedTermRegistry* sharedTermRegistry_ = nullptr;

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

} // namespace nlcolver
