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

namespace xolver {

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

    // setCoreIr / setSharedTermRegistry now live in ArithSolverBase
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

    void allowInterfaceDiseqModelBranch(SharedTermId a, SharedTermId b) override;

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
    // XOLVER_LIA_INCREMENTAL (default OFF): replay only new trail entries into
    // the simplex instead of re-asserting the whole trail every check. See the
    // constructor for rationale (convert / nec-smt LIA-core-scale ceiling).
    bool incrementalEnabled_ = false;

    struct PendingConflict {
        int level;
        TheoryConflict conflict;
    };
    std::optional<PendingConflict> pendingConflict_;

    // coreIr_, sharedTermRegistry_, sharedTermToVarName_ hoisted to
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
    // Canonical (a,b) keys whose decided interface disequality this solver may
    // model-branch (authorized by the combination arrangement split). Static
    // per-solve property; cleared only on reset.
    std::unordered_set<uint64_t> diseqBranchAuthorized_;
    bool safeMode_ = false;
    bool ultraSafeMode_ = false;
    // XOLVER_SIMPLEX_IMPLIED_EQ (default OFF): augment getDeducedSharedEqualities
    // with transitive closure of the variable-variable implied-eq graph. Closes
    // chains x = z and z = y -> x = y over the shared-var graph; reasons are the
    // union of SatLits along the BFS path. Sound by construction.
    // Also gates the LP-duality probe used by the interfaceDisequalities
    // conflict check (Track B fix: extend conflict detection beyond
    // proveFixedValue, mirror of LRA's Track A — needed for Wisa-class
    // pinnings that proveFixedValue's "row vars all fixed" recursion misses).
    bool impliedEqEnabled_ = false;

    // Track A mirror in LIA: per-pair LP-duality probe. Returns true and fills
    // outReasons with the (filtered) Farkas reasons if the polyhedron pins
    // (aux value) == 0; else false. Same RAII / conflict-state-clear /
    // marker-bound-filter discipline as LraSolver::tryProvePairEqualityByLpDuality.
    bool tryProvePairEqualityByLpDuality(int aux, std::vector<SatLit>& outReasons);
    mutable int dumpCounter_ = 0;

    TheoryCheckResult handleDisequalities(TheoryLemmaStorage& lemmaDb);
    TheoryCheckResult checkIntegrality(TheoryLemmaStorage& lemmaDb, TheoryEffort effort);

    // XOLVER_LIA_REPAIR: rounding-based LRA->LIA integrality repair. Read once
    // at construction. When set, checkIntegrality tries rounding the LRA
    // relaxation to a nearby integer point and exact-validating it before
    // branching; a validated point yields SAT immediately.
    bool repairEnabled_ = false;
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

    // XOLVER_LIA_CUTS: Gomory fractional cuts. Read once at construction.
    // generateGomoryCut derives a cut from the fractional basic integer var's
    // tableau row (GomoryCut.h), re-expresses it over original variables, and
    // returns an explanation-aware lemma {¬(bound reasons used), cutLit} — valid
    // for all integer-feasible points (sound regardless of branch). cutsThisSolve_
    // caps cut generation per solve so branch-and-bound still terminates.
    bool cutsEnabled_ = false;
    // XOLVER_LIA_GMI_CUTS (default OFF): use the Gomory Mixed-Integer cut
    // (GomoryCut.h, deriveGmiCut) instead of the pure fractional cut. GMI never
    // bails on a continuous nonbasic (the pure cut returns nullopt there — the
    // common case for second-and-later cuts whose row references a prior cut's
    // fractional-bound slack) and is at least as tight on integer nonbasics, so
    // it strictly widens cut coverage. Sound regardless (brute-force verified).
    bool gmiCutsEnabled_ = false;
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
