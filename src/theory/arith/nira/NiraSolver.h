#pragma once

#include "theory/core/TheorySolver.h"
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

namespace nlcolver {

class TheoryAtomRegistry;

/**
 * NiraSolver: QF_NIRA (Nonlinear Integer-Real Arithmetic) theory solver.
 *
 * Not generally complete. Uses LIRA relaxation, NIA/NRA subproblem delegation,
 * and bounded-complete mode for coverage.
 */
class NiraSolver : public TheorySolver {
public:
    explicit NiraSolver(std::unique_ptr<PolynomialKernel> kernel);
    ~NiraSolver();

    TheoryId id() const override { return TheoryId::NIRA; }

    void push() override;
    void pop(uint32_t n) override;
    void assertLit(const TheoryAtomRecord& atom, bool value, int level, SatLit assertedLit) override;
    void backtrackToLevel(int level) override;
    TheoryCheckResult check(TheoryLemmaStorage& lemmaDb, TheoryEffort effort) override;
    void reset() override;

    void setActiveLinearContext(const std::vector<ActiveLinearConstraint>* context) override {
        activeLinearContext_ = context;
    }

    void setRegistry(TheoryAtomRegistry* reg);
    void setCoreIr(const CoreIr* ir);

    std::optional<TheoryModel> getModel() const override;

private:
    const CoreIr* coreIr_ = nullptr;
    std::unique_ptr<PolynomialKernel> kernel_;
    std::unique_ptr<PolynomialConverter> converter_;
    TheoryAtomRegistry* registry_ = nullptr;

    // Internal linear relaxation engine (not LiraSolver facade)
    GeneralSimplex gsRelax_;
    LinearAtomManager managerRelax_;

    struct ActiveAssignment {
        int level;
        SatLit lit;
        TheoryAtomRecord atom;
        bool value;
    };
    std::vector<ActiveAssignment> activeAssignments_;
    const std::vector<ActiveLinearConstraint>* activeLinearContext_ = nullptr;

    // Check sub-stages
    TheoryCheckResult checkPureSubproblems(TheoryLemmaStorage& lemmaDb);
    TheoryCheckResult checkRelaxationAndValidate(TheoryLemmaStorage& lemmaDb);
    TheoryCheckResult checkBoundedComplete(TheoryLemmaStorage& lemmaDb);

    bool validateOriginalConstraints() const;
    std::vector<SatLit> allActiveReasons() const;

    // Bounded-complete helper: check one integer assignment with fresh simplex
    static bool checkAssignmentWithSimplex(
        const std::vector<ActiveAssignment>& assignments,
        const std::unordered_map<std::string, mpq_class>& fixedValues,
        PolynomialKernel* kernel);
};

} // namespace nlcolver
