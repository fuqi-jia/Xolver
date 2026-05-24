#pragma once

#include "theory/arith/ArithSolverBase.h"
#include "theory/arith/linear/LinearAtomManager.h"
#include "theory/arith/linear/LinearModelValidator.h"
#include "theory/arith/integer/IntegerReasoner.h"
#include "theory/arith/lra/GeneralSimplex.h"
#include "theory/combination/SharedTermRegistry.h"
#include <gmpxx.h>
#include <optional>
#include <unordered_map>
#include <unordered_set>
#include <vector>
#include <string>

namespace nlcolver {

class TheoryAtomRegistry;

class LiaSolver : public ArithSolverBase {
public:
    LiaSolver();
    ~LiaSolver() override;

    TheoryId id() const override { return TheoryId::LIA; }

    // LIA keeps its own incremental cursor trail (theoryTrail_ +
    // appliedCursor_) with simplex/integrality-specific entry data, so it
    // overrides assertLit and routes push/pop/backtrack/reset through the
    // base hooks. check() is the base default driving a single core
    // reasoner.
    void assertLit(const TheoryAtomRecord& atom, bool value, int level, SatLit assertedLit) override;

    void setRegistry(TheoryAtomRegistry* reg) {
        registry_ = reg;
        integerReasoner_.setRegistry(reg);
    }
    void setSafeMode(bool v) {
        safeMode_ = v;
        integerReasoner_.setSafeMode(v);
    }
    void setUltraSafeMode(bool v) { ultraSafeMode_ = v; }
    void setEnableSingleVarTightening(bool v) {
        integerReasoner_.setEnableSingleVarTightening(v);
    }
    void setEnableGcdIneqTightening(bool v) {
        integerReasoner_.setEnableGcdIneqTightening(v);
    }
    void setEnableEqGcdNormalization(bool v) {
        integerReasoner_.setEnableEqGcdNormalization(v);
    }

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
    // Single core reasoner stage (Phase 2): incremental replay + interface
    // equalities + simplex + integrality + branch. Always yields a verdict.
    std::optional<TheoryCheckResult> stageCore(TheoryLemmaStorage& lemmaDb, TheoryEffort effort);

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

    struct LiaTrailEntry {
        int level;
        SatLit lit;
        TheoryAtomRecord atom;
        bool value;
        int auxVar;
        bool isDiseq;
    };
    std::vector<LiaTrailEntry> theoryTrail_;
    size_t appliedCursor_ = 0;

    struct PendingConflict {
        int level;
        TheoryConflict conflict;
    };
    std::optional<PendingConflict> pendingConflict_;

    const CoreIr* coreIr_ = nullptr;
    const SharedTermRegistry* sharedTermRegistry_ = nullptr;

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

    std::unordered_map<uint64_t, int> interfaceEqAuxVars_;
    bool safeMode_ = false;
    bool ultraSafeMode_ = false;
    mutable int dumpCounter_ = 0;

    TheoryCheckResult handleDisequalities(TheoryLemmaStorage& lemmaDb);
    TheoryCheckResult checkIntegrality(TheoryLemmaStorage& lemmaDb);

    TheoryLemma buildBranchSplitLemma(int var, const DeltaRational& val);

    void dumpState(const std::string& tag) const;
    static std::string linearFormToSmtLib(const LinearFormKey& form);
    static std::string mpqToSmtLib(const mpq_class& q);
    static std::string relationToSmtLib(Relation rel);
    std::optional<bool> z3CheckCurrentState() const;

    std::string getVarNameForSharedTerm(SharedTermId s);
    int getOrCreateInterfaceEqAuxVar(SharedTermId a, SharedTermId b);

    std::vector<SatLit> allActiveReasons() const;
};

} // namespace nlcolver
