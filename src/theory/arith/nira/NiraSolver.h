#pragma once

#include "theory/arith/ArithSolverBase.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include "theory/arith/poly/PolynomialConverter.h"
#include "theory/arith/lra/GeneralSimplex.h"
#include "theory/arith/linear/LinearAtomManager.h"
#include "expr/types.h"
#include <gmpxx.h>
#include <memory>
#include <vector>
#include <optional>
#include <unordered_set>

namespace zolver {

class TheoryAtomRegistry;

/**
 * NiraSolver: QF_NIRA (Nonlinear Integer-Real Arithmetic) theory solver.
 *
 * Not generally complete. Uses LIRA relaxation, NIA/NRA subproblem delegation,
 * and bounded-complete mode for coverage.
 */
class NiraSolver : public ArithSolverBase {
public:
    explicit NiraSolver(std::unique_ptr<PolynomialKernel> kernel);
    ~NiraSolver();

    TheoryId id() const override { return TheoryId::NIRA; }

    TheoryCheckResult check(TheoryLemmaStorage& lemmaDb, TheoryEffort effort) override;

    void setActiveLinearContext(const std::vector<ActiveLinearConstraint>* context) override {
        activeLinearContext_ = context;
    }

    void setRegistry(TheoryAtomRegistry* reg);
    void setCoreIr(const CoreIr* ir);

    std::optional<TheoryModel> getModel() const override;

protected:
    void onPush() override;
    void onPop(uint32_t n) override;
    void onBacktrack(int targetLevel) override;
    void onReset() override;

private:
    const CoreIr* coreIr_ = nullptr;
    std::unique_ptr<PolynomialKernel> kernel_;
    std::unique_ptr<PolynomialConverter> converter_;
    TheoryAtomRegistry* registry_ = nullptr;

    // Internal linear relaxation engine (not LiraSolver facade)
    GeneralSimplex gsRelax_;
    LinearAtomManager managerRelax_;

    const std::vector<ActiveLinearConstraint>* activeLinearContext_ = nullptr;

    // Witness assembled when a sub-engine reports sat, returned by
    // getModel(). NIRA used to always return nullopt, so the user-facing
    // model fell back to the LIRA linearization helper (linear-feasible,
    // ignores the nonlinear constraints). currentModel_ carries the real
    // witness (rational or algebraic via RealValue) plus fixed integers.
    std::optional<TheoryModel> currentModel_;

    // Check sub-stages
    TheoryCheckResult checkPureSubproblems(TheoryLemmaStorage& lemmaDb);
    TheoryCheckResult checkRelaxationAndValidate(TheoryLemmaStorage& lemmaDb);
    TheoryCheckResult checkBoundedComplete(TheoryLemmaStorage& lemmaDb);

    bool validateOriginalConstraints() const;
    std::vector<SatLit> allActiveReasons() const;

    enum class AssignmentCheckResult { Sat, Unsat, Unknown };

    // Bounded-complete helper: check one integer assignment with fresh simplex.
    // linearCtx carries LIRA constraints that bound real variables.
    static AssignmentCheckResult checkAssignmentWithSimplex(
        const std::vector<ActiveAssignment>& assignments,
        const std::vector<ActiveLinearConstraint>* linearCtx,
        const std::unordered_map<std::string, mpq_class>& fixedValues,
        PolynomialKernel* kernel);
};

} // namespace zolver
