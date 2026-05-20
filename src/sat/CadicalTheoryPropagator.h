#pragma once

#ifdef NLCOLVER_HAS_CADICAL

#include <cadical.hpp>
#include "theory/core/TheoryPropagatorCallbacks.h"
#include <chrono>
#include <deque>

#ifdef NLCOLVER_ENABLE_CASESTATS
#include "util/CaseStats.h"
#endif

namespace nlcolver {

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

    bool cb_has_external_clause(bool& is_forgettable) override;
    int cb_add_external_clause_lit() override;

    void setUnknownReasonSink(std::string* sink);

    const TheorySearchStats& stats() const { return stats_; }

#ifdef NLCOLVER_ENABLE_CASESTATS
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
    static constexpr int MAX_MODEL_CHECKS = 10000;
    CadicalAssignmentView assignmentView_;
    CadicalAssignmentView partialAssignmentView_;
    std::string* unknownReasonSink_ = nullptr;
    std::unordered_map<SatVar, int> varToLevel_;
    std::unordered_map<SatVar, bool> currentAssignment_;
    size_t lastCheckedAssignmentSize_ = 0;

    TheorySearchStats stats_;

#ifdef NLCOLVER_ENABLE_CASESTATS
    CaseStats* caseStats_ = nullptr;
    std::string dumpStatsBasePath_;
    HeartbeatWriter heartbeatWriter_;
#endif

    CadicalAssignmentView& assignmentView() { return assignmentView_; }

#ifdef NLCOLVER_ENABLE_CASESTATS
    void updateCaseStatsSearch();
#endif

    void enqueuePendingClause(const std::vector<SatLit>& lits);
    void enqueuePendingClause(const TheoryLemma& lemma);
    void terminateSolve();
    bool isClauseFalsifiedByCurrentModel(const std::vector<SatLit>& clause) const;
};

} // namespace nlcolver

#endif // NLCOLVER_HAS_CADICAL
