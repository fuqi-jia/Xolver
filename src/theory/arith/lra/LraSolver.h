#pragma once

#include "theory/TheorySolver.h"
#include "theory/arith/linear/LinearAtomManager.h"
#include "GeneralSimplex.h"
#include <gmpxx.h>
#include <unordered_map>
#include <vector>
#include <string>

namespace nlcolver {

class LraSolver : public TheorySolver {
public:
    LraSolver();

    TheoryId id() const override { return TheoryId::LRA; }

    void push() override;
    void pop(uint32_t n) override;
    void assertLit(const TheoryAtomRecord& atom, bool value, int level, SatLit reason) override;
    void backtrackToLevel(int level) override;
    TheoryCheckResult check(TheoryLemmaDatabase& lemmaDb) override;
    void reset() override;

private:
    GeneralSimplex gs_;
    LinearAtomManager manager_;

    struct DiseqInfo {
        int auxVar;
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

    TheoryCheckResult handleDisequalities();
    TheoryLemma buildDiseqSplitLemma(const DiseqInfo& d);
};

} // namespace nlcolver
