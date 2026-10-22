#pragma once

#include "search/arith/ArithSolverBase.h"
#include "search/linear/LinearAtomManager.h"
#include "search/linear/LinearModelValidator.h"
#include "search/linear/IntegerReasoner.h"
#include "search/lra/GeneralSimplex.h"
#include "search/combination/SharedTermRegistry.h"
#include <gmpxx.h>
#include <optional>
#include <unordered_map>
#include <unordered_set>
#include <vector>
#include <string>

namespace xolver {

class TheoryAtomRegistry;

class LiaSolver : public ArithSolverBase {
public:
    LiaSolver();
    ~LiaSolver() override;

    TheoryId id() const override { return TheoryId::LIA; }

    // LIA keeps its own theory trail (theoryTrail_ +
    // active-atom caches) with simplex/integrality-specific entry data, so it
    // overrides assertLit and routes push/pop/backtrack/reset through the
    // base hooks. check() is the base default driving a single core
    // reasoner.
    void assertLit(const TheoryAtomRecord& atom, bool value, int level, SatLit assertedLit) override;

    void setRegistry(TheoryAtomRegistry* reg) {
        registry_ = reg;
        integerReasoner_.setRegistry(reg);
    }
    // setNativeTerms / setSharedTermRegistry now live in ArithSolverBase
    // (hoisted 2026-06-04 with getVarNameForSharedTerm).

    bool supportsCombination() const override { return true; }

    TheoryCheckResult assertInterfaceEquality(
        SharedTermId a, SharedTermId b, SatLit reason, int level) override;
    TheoryCheckResult assertInterfaceDisequality(
        SharedTermId a, SharedTermId b, SatLit reason, int level) override;

    std::vector<SharedEqualityPropagation>
    getDeducedSharedEqualities() override;

    // Entailment propagations buffered during check(). Drained by
    // TheoryManager::takeEntailmentPropagations and forwarded to SAT as
    // unit/learned clauses. Wisa-class closure depends on this: when
    // bridge_J_i is pinned to a value via N-O propagation from EUF and an
    // unassigned LIA equality atom `(= bridge_J_i c)` exists, this propagates
    // the atom to true (or false on value mismatch), forcing SAT to honor
    // the consequence and closing the goal-atom escape that the floor
    // currently catches as a SAT model violating the original assertion.
    std::vector<TheoryLemma> takeEntailmentPropagations() override;

    std::vector<SharedEqualityPropagation>
    deduceIndexEqualitiesByGaussian(const std::vector<SharedTermId>& idxTerms) override;

    std::optional<RealValue> sharedTermArithValue(SharedTermId s) const override;


    std::optional<TheoryModel> getModel() const override;
    // Like getModel() but also reports internal/aux variables (names starting
    // with "__"). Used by NiaSolver's embedded linear-decide to obtain the
    // COMPLETE assignment for exact re-validation against NIA's normalized
    // constraints (which reference NIA's mod/div-lowering aux vars).
    std::optional<TheoryModel> getModelWithInternal() const;

    // Standalone complete integer solve for NiaSolver's embedded linear-decide.
    // Precondition: the caller has asserted all constraints via assertLit. Runs
    // one Full check (LP + integrality repair); if that leaves a fractional
    // branch, drives branch-and-bound over gs_ directly (no SAT loop) up to
    // nodeCap nodes. Returns the COMPLETE integer model (incl. internal vars)
    // on SAT, or nullopt (UNSAT-on-input / Unknown / node cap).
    //
    // If outConflict is non-null AND the ROOT LP relaxation is infeasible
    // (Farkas-certified), *outConflict is set to that conflict — a genuine
    // infeasibility of the asserted atoms whose reason literals are exactly the
    // ones the caller passed to assertLit (real SAT literals). A B&B node cap or
    // integrality-only infeasibility does NOT set it (that is not a proven
    // conflict). The caller may return *outConflict as a sound theory conflict.
    std::optional<TheoryModel> findIntegerModel(
        int nodeCap = 4000, std::optional<TheoryConflict>* outConflict = nullptr);

    // Explained fixed-value query. After the caller has asserted
    // its constraints (assertLit) and run a check() so gs_ is pivoted, this
    // returns the fixed (pinned) value of variable `name` together with the
    // asserted SAT literals whose bounds force it, or nullopt if the variable is
    // not pinned to a single rational value. Each returned reason is a real
    // asserted literal (every bound was asserted with the caller's SatLit), so
    // `(∧reasons) → (name == value)` is a valid theory tautology. A δ-strict
    // (open) pin returns nullopt.
    std::optional<std::pair<mpq_class, std::vector<SatLit>>>
    proveFixedValueByName(const std::string& name) const;

    // Like proveFixedValueByName but for a whole linear FORM: returns the pinned
    // value of `(lhs - rhs)` together with its asserted reasons, or nullopt if
    // the form is not pinned to a single value. This is the variable–variable
    // equality channel (e.g. `x - y` pinned to 0 when x ≤ y ∧ y ≤ x are asserted,
    // even though neither x nor y is individually pinned). NOT const: it
    // getOrCreate's the form's aux variable in the simplex (a scratch instance).
    std::optional<std::pair<mpq_class, std::vector<SatLit>>>
    proveFixedFormValue(const LinearFormKey& lhs, const mpq_class& rhs);

protected:
    void onPush() override;
    void onPop(uint32_t n) override;
    void onBacktrack(int targetLevel) override;
    void onReset() override;

private:
    // Single core reasoner stage: trail replay + interface
    // equalities + simplex + integrality + branch. Always yields a verdict.
    std::optional<TheoryCheckResult> stageCore(TheoryLemmaStorage& lemmaDb, TheoryEffort effort);

    // Shared model builder; includeInternal keeps "__"-prefixed aux vars.
    std::optional<TheoryModel> buildModel(bool includeInternal) const;

    // Recursive branch-and-bound over gs_ integer vars for findIntegerModel().
    std::optional<TheoryModel> branchAndBound(int nodeCap, int& nodes);

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
    // satVar -> theoryTrail_ index for O(1) lookup in assertLit's update path.
    // assertLit's hot path used to linear-scan theoryTrail_ to find an existing
    // entry for the same satVar (e->update vs append). On large QF_LIA loads
    // (Dartagnan ReachSafety-Loops, elster B_1: 17-22 k atoms after preprocess)
    // that scan is O(N) per assertLit call -- O(N^2) per SAT decision -- and was
    // the dominant cost on these cases (60s wall, only 5s in lia.core; ~90%
    // outside theory check). Keep this map in lockstep with theoryTrail_:
    // assertLit, onBacktrack, reset, and the level-trim path must all update it.
    std::unordered_map<uint32_t, size_t> trailIndexBySatVar_;
    struct PendingConflict {
        int level;
        TheoryConflict conflict;
    };
    std::optional<PendingConflict> pendingConflict_;

    // nativeTerms_, sharedTermRegistry_, sharedTermToVarName_ hoisted to
    // ArithSolverBase (2026-06-04 with getVarNameForSharedTerm).

    // Buffered entailment lemmas; drained by takeEntailmentPropagations().
    std::vector<TheoryLemma> entailmentProps_;
    // Per-(satVar, value) dedup — emit each entailment at most once per
    // SAT-decision cycle. Cleared on backtrack to level 0 / reset.
    std::unordered_set<uint64_t> entailmentEmittedKeys_;
    void scanLiteralPinEntailments();
    void clearEntailmentDedupForBacktrack(int level);

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
    mutable int dumpCounter_ = 0;

    TheoryCheckResult handleDisequalities(TheoryLemmaStorage& lemmaDb);
    TheoryCheckResult checkIntegrality(TheoryLemmaStorage& lemmaDb, TheoryEffort effort);

    // Holds the repaired integer model (var name -> integer value) when a repair
    // succeeded this check. Set only by checkIntegrality, consumed by getModel /
    // the SAT path in stageCore, cleared at the start of each stageCore and on
    // reset/backtrack.
    std::optional<std::unordered_map<std::string, mpq_class>> repairModel_;
    // Try the round-to-nearest integer point of the current LRA model; if it
    // satisfies every active atom and disequality exactly, store it in
    // repairModel_ and return true.
    bool tryIntegralityRepair();
    // Exact evaluation of all active atoms + disequalities at an integer point.
    bool pointSatisfiesAll(const std::unordered_map<std::string, mpq_class>& pt) const;

    TheoryLemma buildBranchSplitLemma(int var, const DeltaRational& val);

    // Explanation-carrying cuts are capped per solve before integer splitting.
    int cutsThisSolve_ = 0;
    std::optional<TheoryLemma> generateGomoryCut(int basicVar);
    // True iff the simplex variable is provably integer-valued (original integer
    // var, or an aux whose defining form has integer coeffs/rhs over integer vars).
    bool isSimplexVarInteger(int idx) const;

    void dumpState(const std::string& tag) const;
    static std::string linearFormToSmtLib(const LinearFormKey& form);
    static std::string mpqToSmtLib(const mpq_class& q);
    static std::string relationToSmtLib(Relation rel);

    // getVarNameForSharedTerm hoisted to ArithSolverBase (2026-06-04).
    int getOrCreateInterfaceEqAuxVar(SharedTermId a, SharedTermId b);

    // If the asserted linear (in)equality atoms entail that the two shared
    // terms a and b are equal — either via an explicit 2-var equality atom
    // (c*x - c*y = 0, e.g. (+i1)=(+j1)) or via two complementary inequalities
    // pinning the difference to 0 (x<=y ∧ y<=x) — return the reason literals of
    // the pinning atoms. Empty if no such entailment is found. Used both to
    // propagate implied shared equalities and to refute an interface
    // disequality x!=y that contradicts the entailed x=y.
    std::vector<SatLit> assertedVarEqualityReason(SharedTermId a, SharedTermId b) const;

    std::vector<SatLit> allActiveReasons() const;
};

} // namespace xolver
