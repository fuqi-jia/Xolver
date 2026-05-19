#pragma once

#include "theory/core/TheorySolver.h"
#include "theory/arith/linear/LinearAtomManager.h"
#include "theory/arith/lra/GeneralSimplex.h"
#include "theory/arith/lia/InternalMilpEngine.h"
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
 * Delegates to InternalMilpEngine with different solve policies:
 *   - Standard effort: Budgeted mode (LP relaxation + bounded branch-and-bound,
 *     may return NeedBranch for lemma generation).
 *   - Full effort: Complete mode (exhaustive branch-and-bound final decision).
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
    TheoryCheckResult check(TheoryLemmaStorage& lemmaDb, TheoryEffort effort) override;
    void reset() override;

    void setRegistry(TheoryAtomRegistry* reg);
    void setCoreIr(const CoreIr* ir);

    std::optional<TheoryModel> getModel() const override;

private:
    // Legacy fields kept to avoid breaking compilation of other TU references.
    // New code uses milpEngine_ exclusively.
    GeneralSimplex gsRelax_;
    LinearAtomManager managerRelax_;
    GeneralSimplex gsReconstruct_;
    LinearAtomManager managerReconstruct_;
    std::vector<int> liraVarToSimplexColRelax_;
    std::unordered_map<uint64_t, int> coreVarToLiraVar_;
    std::vector<uint64_t> liraVarToCoreVar_;
    std::vector<SortKind> liraVarSort_;

    // Active MILP engine
    InternalMilpEngine milpEngine_;

    // CDCL state
    TheoryAtomRegistry* registry_ = nullptr;
    const CoreIr* coreIr_ = nullptr;

    struct DiseqInfo {
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
    TheoryCheckResult checkStandardEffort(TheoryLemmaStorage& lemmaDb);
    TheoryCheckResult checkFullEffort(TheoryLemmaStorage& lemmaDb);

    // Helpers
    bool isIntegerVar(const std::string& name) const;
    std::vector<SatLit> allActiveReasons() const;
    void dumpUnsatAssignment(const std::string& prefix) const;
};

} // namespace nlcolver
