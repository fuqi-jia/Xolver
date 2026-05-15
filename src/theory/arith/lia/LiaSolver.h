#pragma once

#include "theory/TheorySolver.h"
#include "theory/arith/linear/LinearAtomManager.h"
#include "theory/arith/linear/LinearModelValidator.h"
#include "theory/arith/linear/IntegerReasoner.h"
#include "theory/arith/lra/GeneralSimplex.h"
#include <gmpxx.h>
#include <unordered_map>
#include <unordered_set>
#include <vector>
#include <string>

namespace nlcolver {

class TheoryAtomRegistry;

class LiaSolver : public TheorySolver {
public:
    LiaSolver();

    TheoryId id() const override { return TheoryId::LIA; }

    void push() override;
    void pop(uint32_t n) override;
    void assertLit(const TheoryAtomRecord& atom, bool value, int level, SatLit assertedLit) override;
    void backtrackToLevel(int level) override;
    TheoryCheckResult check(TheoryLemmaDatabase& lemmaDb) override;
    void reset() override;

    void setRegistry(TheoryAtomRegistry* reg) {
        registry_ = reg;
        integerReasoner_.setRegistry(reg);
    }

private:
    GeneralSimplex gs_;
    LinearAtomManager manager_;
    TheoryAtomRegistry* registry_ = nullptr;

    std::unordered_set<int> integerVars_;

    struct DiseqInfo {
        int auxVar;
        LinearFormKey lhs;
        mpq_class rhs;
        SatLit lit;
    };
    std::vector<DiseqInfo> disequalities_;

    std::vector<ActiveLinearAtom> activeAtoms_;
    LinearModelValidator validator_;
    IntegerReasoner integerReasoner_;

    struct ActiveAssignment {
        int level;
        SatLit lit;
        TheoryAtomRecord atom;
        bool value;
    };
    std::vector<ActiveAssignment> activeAssignments_;

    struct PendingConflict {
        int level;
        TheoryConflict conflict;
    };
    std::optional<PendingConflict> pendingConflict_;

    TheoryCheckResult handleDisequalities(TheoryLemmaDatabase& lemmaDb);
    TheoryCheckResult checkIntegrality(TheoryLemmaDatabase& lemmaDb);

    TheoryLemma buildDiseqSplitLemma(const DiseqInfo& d);
    TheoryLemma buildBranchSplitLemma(int var, const DeltaRational& val);
};

} // namespace nlcolver
