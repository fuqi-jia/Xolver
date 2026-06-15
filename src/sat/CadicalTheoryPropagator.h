#pragma once

#include <cadical.hpp>
#include "theory/core/TheoryPropagatorCallbacks.h"
#include <chrono>
#include <deque>

namespace xolver { class RelevancyEngine; }

#ifdef XOLVER_ENABLE_CASESTATS
#include "util/CaseStats.h"
#endif

namespace xolver {

/**
 * Search statistics collected during SAT + theory solving.
 * Printed at the end of solve() for diagnostics.
 */
struct TheorySearchStats {
    // --- modelCheck (Full effort) ---
    int modelCheckCount = 0;
    long long modelCheckTotalUs = 0;
    int modelCheckConsistent = 0;
    int modelCheckConflict = 0;
    int modelCheckLemma = 0;
    int modelCheckUnknown = 0;
    int conflictMinSize = -1;
    int conflictMaxSize = 0;
    long long conflictTotalSize = 0;

    // --- cb_propagate (Standard effort) ---
    int propagateCallCount = 0;
    int propagateTheoryCheckCount = 0;
    int propagateConflictCount = 0;
    int propagateLemmaCount = 0;
    int propagateConflictMinSize = -1;
    int propagateConflictMaxSize = 0;
    long long propagateConflictTotalSize = 0;
    long long propagateCheckTotalUs = 0;

    void recordModelCheck(bool ok, std::chrono::microseconds dur);
    void recordModelCheckResult(TheoryCheckResult::Kind kind, int conflictSize);
    void recordPropagateCheck(bool conflict, bool lemma, int conflictSize, std::chrono::microseconds dur);
    void print(std::ostream& out) const;
};

class CadicalBackend;

/**
 * Lightweight assignment view populated from CaDiCaL's cb_check_found_model model.
 * Safe to query from TheoryManager::check() because it does not call back into CaDiCaL.
 */
class CadicalAssignmentView : public TheoryAssignmentView {
public:
    void clear() { values_.clear(); }
    void setVarValue(SatVar var, bool value) {
        if (var >= values_.size()) values_.resize(var + 1, 0);
        values_[var] = value ? 1 : -1;
    }
    LitValue value(SatLit lit) const override {
        if (lit.var >= values_.size()) return LitValue::Unknown;
        int v = values_[lit.var];
        if (v == 0) return LitValue::Unknown;
        bool varTrue = (v > 0);
        bool litTrue = lit.sign ? varTrue : !varTrue;
        return litTrue ? LitValue::True : LitValue::False;
    }
private:
    std::vector<int8_t> values_;
};

/**
 * CadicalTheoryPropagator: bridges CaDiCaL's ExternalPropagator to our theory stack.
 */
class CadicalTheoryPropagator : public CaDiCaL::ExternalPropagator {
public:
    CadicalTheoryPropagator(
        TheoryAtomLookup& registry,
        TheoryPropagationCallbacks& tm,
        TheoryLemmaStorage& lemmaDb,
        CadicalBackend& backend
    );

    // --- IPASIR-UP callbacks ---
    void notify_assignment(const std::vector<int>& lits) override;
    void notify_new_decision_level() override;
    void notify_backtrack(size_t new_level) override;

    bool cb_check_found_model(const std::vector<int>& model) override;
    int cb_propagate() override;

    // Behavior-neutral decision-steering PROBE (returns 0 = decline; CaDiCaL
    // decides as normal, so OFF==ON). Counts decision requests and, via the
    // first assignment after each new decision level, buckets decisions into
    // theory bound-atoms vs boolean-structure literals. Periodic stderr dump
    // gated by env XOLVER_DECIDE_PROBE. Measures whether decision-steering has
    // any leverage before building a real cb_decide steering heuristic.
    int cb_decide() override;

    bool cb_has_external_clause(bool& is_forgettable) override;
    int cb_add_external_clause_lit() override;

    void setUnknownReasonSink(std::string* sink);

    // L7: attach a finalized relevancy engine to steer cb_decide toward the
    // relevant boolean skeleton (XOLVER_RELEVANCY). Pure decision heuristic —
    // never changes satisfiability. The engine must outlive solve(); its value
    // oracle is wired here to read this propagator's live assignment.
    void setRelevancyEngine(RelevancyEngine* rel);

    const TheorySearchStats& stats() const { return stats_; }

#ifdef XOLVER_ENABLE_CASESTATS
    // --- CaseStats integration ---
    void setCaseStats(CaseStats* stats) { caseStats_ = stats; }
    void setDumpStatsBasePath(const std::string& path) { dumpStatsBasePath_ = path; }
#endif

private:
    TheoryAtomLookup& registry_;
    TheoryPropagationCallbacks& tm_;
    TheoryLemmaStorage& lemmaDb_;
    CadicalBackend& backend_;

    int currentLevel_ = 0;
    std::deque<std::vector<SatLit>> pendingClauses_;
    std::vector<SatLit> currentPendingClause_;
    size_t currentPendingClausePos_ = 0;
    bool hasPendingClause_ = false;
    bool abortWithUnknown_ = false;
    // Backstop against a pathologically looping theory solver (same model
    // re-proposed without progress), NOT a performance budget. The real budget
    // guard is the competition wall-clock (1200s) + the watchdog terminate; a
    // hard combination/array problem can legitimately need far more than 10k
    // Full-effort model refinements within 1200s, so the old dev-conservative
    // 10k fuse cut off solvable instances (-> unknown) well before the budget.
    // Retuned to the 1200s/30GB budget: high enough that the wall-clock dominates
    // for genuine work, still finite so a true infinite loop is bounded. Sound to
    // raise — the fuse only ever yields `unknown`, never a wrong verdict.
    static constexpr int MAX_MODEL_CHECKS = 10000000;
    CadicalAssignmentView assignmentView_;
    CadicalAssignmentView partialAssignmentView_;
    std::string* unknownReasonSink_ = nullptr;
    std::unordered_map<SatVar, int> varToLevel_;
    std::unordered_map<SatVar, bool> currentAssignment_;
    size_t lastCheckedAssignmentSize_ = 0;
    // Set true whenever a theory *atom* is asserted (notify_assignment); cleared
    // when cb_propagate runs a Standard check. When the cb_propagate throttle
    // fires on pure-boolean growth (no atom asserted since the last check, no
    // backtrack), the theory atom-set is unchanged, so the check + O(n) view
    // rebuild are skipped — provably the same result (a non-backtrack check on an
    // unchanged atom-set that found a conflict/propagation would have changed the
    // atom-set or backtracked, so the re-check returns 0). This is unconditional
    // (verdict-identical, not a tunable). Starts true so the first check runs.
    bool theoryDirtySinceCheck_ = true;

    // Soundness floor (XOLVER_SAT_DEFER_EARLY_CONFLICT). In combination mode a
    // Standard-effort cb_propagate theory conflict is UNVALIDATED (conflictIsGenuine
    // only re-verifies pure shared-equality conflicts; a mixed/theory conflict is
    // trusted), so an unsound theory conflict can drive a false UNSAT. When set,
    // such early conflicts are suppressed so the search proceeds to a complete
    // model and the authoritative Full-effort model check arbitrates. Sound on its
    // own; intent default-ON at integration, flag for perf A/B.
    bool deferEarlyConflict_ = false;
    // Decision-steering probe counters (instrumentation only).
    long long decideCalls_ = 0;        // cb_decide invocations (= decision points)
    long long decisionLits_ = 0;       // decisions observed via notify
    long long theoryAtomDecisions_ = 0;// of those, over a linear bound atom
    bool expectDecisionLit_ = false;   // next notify_assignment's first lit is the decision

    // XOLVER_LRA_DECIDE (default OFF): steer decisions toward a theory-feasible
    // region by returning an unassigned bound-atom literal at its
    // feasibility-consistent phase. Heuristic — soundness-safe.
    bool decideSteer_ = false;
    // L7 relevancy steering (XOLVER_RELEVANCY). rel_ is borrowed (owned by the
    // caller's scope); relevancyOn_ gates all relevancy work so OFF == zero cost.
    RelevancyEngine* rel_ = nullptr;
    bool relevancyOn_ = false;
    long long relSteeredDecisions_ = 0;  // decisions returned by relevancy
    bool theoryAtomVarsBuilt_ = false;
    std::vector<SatVar> theoryAtomVars_;
    size_t decideCursor_ = 0;
    // cb_decide free-observed-atom fallback (XOLVER_COMB_DECIDE_FREE_ATOMS):
    // cached snapshot of all atom SatVars + the registry size it was taken at
    // (rebuild when atoms are created mid-solve) + a round-robin scan cursor.
    std::vector<SatVar> allAtomVars_;
    size_t allAtomVarsSize_ = SIZE_MAX;  // != registry size => rebuild
    size_t freeAtomCursor_ = 0;
    long long freeAtomDecisions_ = 0;
    long long steeredDecisions_ = 0;
    long long dbgUnassignedProbes_ = 0;
    long long dbgEvalNull_ = 0;

    TheorySearchStats stats_;

#ifdef XOLVER_ENABLE_CASESTATS
    CaseStats* caseStats_ = nullptr;
    std::string dumpStatsBasePath_;
    HeartbeatWriter heartbeatWriter_;
#endif

    CadicalAssignmentView& assignmentView() { return assignmentView_; }

#ifdef XOLVER_ENABLE_CASESTATS
    void updateCaseStatsSearch();
#endif

    void enqueuePendingClause(const std::vector<SatLit>& lits);
    void enqueuePendingClause(const TheoryLemma& lemma);
    void terminateSolve();
    bool isClauseFalsifiedByCurrentModel(const std::vector<SatLit>& clause) const;
};

} // namespace xolver
