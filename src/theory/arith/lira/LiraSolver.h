#pragma once

#include "theory/TheorySolver.h"
#include "theory/arith/linear/LinearAtomManager.h"
#include "theory/arith/lra/GeneralSimplex.h"
#include "expr/types.h"
#include <gmpxx.h>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace nlcolver {

class TheoryAtomRegistry;

/**
 * LiraSolver: QF_LIRA (Linear Integer-Real Arithmetic) theory solver.
 *
 * Main algorithm: exact rational LP relaxation + branch-and-cut / MILP-style engine.
 * FM is only used as optional small-case equality elimination, not as the complete path.
 */
class LiraSolver : public TheorySolver {
public:
    LiraSolver();
    ~LiraSolver();

    TheoryId id() const override { return TheoryId::LIRA; }

    void push() override;
    void pop(uint32_t n) override;
    void assertLit(const TheoryAtomRecord& atom, bool value, int level, SatLit assertedLit) override;
    void backtrackToLevel(int level) override;
    TheoryCheckResult check(TheoryLemmaDatabase& lemmaDb, TheoryEffort effort) override;
    void reset() override;

    void setRegistry(TheoryAtomRegistry* reg);
    void setCoreIr(const CoreIr* ir);

    std::optional<TheoryModel> getModel() const override;

private:
    // Variable management: CoreVarId -> LiraVarId
    std::unordered_map<uint64_t, int> coreVarToLiraVar_;
    std::vector<uint64_t> liraVarToCoreVar_;
    std::vector<SortKind> liraVarSort_;
    int getOrCreateLiraVar(uint64_t coreVarId, SortKind sort);

    // Relaxation simplex
    GeneralSimplex gsRelax_;
    LinearAtomManager managerRelax_;
    std::vector<int> liraVarToSimplexColRelax_;

    // Reconstruction simplex (state isolation)
    GeneralSimplex gsReconstruct_;
    LinearAtomManager managerReconstruct_;

    // CDCL state
    TheoryAtomRegistry* registry_ = nullptr;
    const CoreIr* coreIr_ = nullptr;
    std::unordered_set<int> integerVars_; // simplex column indices of Int vars

    struct DiseqInfo {
        int auxVar;
        LinearFormKey lhs;
        mpq_class rhs;
        SatLit lit;
    };
    std::vector<DiseqInfo> disequalities_;

    struct ActiveAssignment {
        int level;
        SatLit lit;
        TheoryAtomRecord atom;
        bool value;
    };
    std::vector<ActiveAssignment> activeAssignments_;

    // Check sub-stages
    TheoryCheckResult checkStandardEffort(TheoryLemmaDatabase& lemmaDb);
    TheoryCheckResult checkFullEffort(TheoryLemmaDatabase& lemmaDb);

    bool buildRelaxationBounds();
    bool isRelaxationIntegral() const;
    bool validateFullModel() const;
    std::optional<TheoryLemma> tryGenerateBranchLemma();

    // Utilities
    std::vector<SatLit> allActiveReasons() const;
    DeltaRational getRelaxationValue(int liraVarId) const;
};

} // namespace nlcolver
