#pragma once

#include "theory/core/TheorySolver.h"
#include "theory/core/TheoryAtomRegistry.h"
#include "theory/arith/linear/LinearAtomManager.h"
#include "theory/combination/SharedTermRegistry.h"
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
    void assertLit(const TheoryAtomRecord& atom, bool value, int level, SatLit assertedLit) override;
    void backtrackToLevel(int level) override;
    TheoryCheckResult check(TheoryLemmaStorage& lemmaDb, TheoryEffort effort = TheoryEffort::Standard) override;
    void reset() override;

    void setCoreIr(const CoreIr* ir) { coreIr_ = ir; }
    void setSharedTermRegistry(const SharedTermRegistry* reg) { sharedTermRegistry_ = reg; }
    void setRegistry(TheoryAtomRegistry* reg) { registry_ = reg; }

    // Nelson-Oppen combination hooks
    bool supportsCombination() const override { return true; }

    TheoryCheckResult assertInterfaceEquality(
        SharedTermId a, SharedTermId b, SatLit reason, int level) override;
    TheoryCheckResult assertInterfaceDisequality(
        SharedTermId a, SharedTermId b, SatLit reason, int level) override;

    std::vector<SharedEqualityPropagation>
    getDeducedSharedEqualities() override;

    std::optional<TheoryModel> getModel() const override;

private:
    GeneralSimplex gs_;
    LinearAtomManager manager_;

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

    const CoreIr* coreIr_ = nullptr;
    const SharedTermRegistry* sharedTermRegistry_ = nullptr;

    // Map from SharedTermId to variable name for simplex
    std::unordered_map<SharedTermId, std::string> sharedTermToVarName_;

    struct InterfaceEq {
        SharedTermId a;
        SharedTermId b;
        SatLit reason;
        int level;
    };
    std::vector<InterfaceEq> interfaceEqualities_;
    std::vector<InterfaceEq> interfaceDisequalities_;
    int currentLevel_ = 0;

    // Map from (a,b) canonical key to auxiliary var index for x - y
    std::unordered_map<uint64_t, int> interfaceEqAuxVars_;

    TheoryCheckResult handleDisequalities(TheoryLemmaStorage& lemmaDb);

    std::string getVarNameForSharedTerm(SharedTermId s);
    int getOrCreateInterfaceEqAuxVar(SharedTermId a, SharedTermId b);

    TheoryAtomRegistry* registry_ = nullptr;

    std::vector<SatLit> allActiveReasons() const;
};

} // namespace nlcolver
