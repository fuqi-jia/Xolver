#pragma once

#include "theory/arith/ArithSolverBase.h"
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
class LiraSolver : public ArithSolverBase {
public:
    LiraSolver();
    ~LiraSolver();

    TheoryId id() const override { return TheoryId::LIRA; }

    TheoryCheckResult check(TheoryLemmaStorage& lemmaDb, TheoryEffort effort) override;

    void setRegistry(TheoryAtomRegistry* reg);
    void setCoreIr(const CoreIr* ir);

    std::optional<TheoryModel> getModel() const override;

protected:
    void onPush() override;
    void onPop(uint32_t n) override;
    void onReset() override;

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

    // Check sub-stages
    TheoryCheckResult checkStandardEffort(TheoryLemmaStorage& lemmaDb);
    TheoryCheckResult checkFullEffort(TheoryLemmaStorage& lemmaDb);

    // Helpers
    bool isIntegerVar(const std::string& name) const;
    std::vector<SatLit> allActiveReasons() const;

    // Cache for isIntegerVar: scanning the whole CoreIr per variable per check
    // is O(IR x vars x checks). Build a name->isInt map once and rebuild only
    // when the IR grows (sorts are immutable, so entries never go stale).
    mutable std::unordered_map<std::string, bool> intVarCache_;
    mutable size_t intVarCacheIrSize_ = 0;
    void ensureIntVarCache() const;
};

} // namespace nlcolver
