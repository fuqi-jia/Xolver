#include "sat/CadicalTheoryPropagator.h"
#include "sat/CadicalBackend.h"
#include <cassert>
#include <iostream>
#include <iomanip>

// Inline replacement for theory/core/DebugTrace.h to avoid sat/ -> theory/ include.
#define NO_DBG if (true) {} else std::cerr

namespace nlcolver {

// ------------------------------------------------------------------
// TheorySearchStats implementation
// ------------------------------------------------------------------

void TheorySearchStats::recordModelCheckResult(TheoryCheckResult::Kind kind, int conflictSize) {
    ++modelCheckCount;
    switch (kind) {
        case TheoryCheckResult::Kind::Consistent: ++modelCheckConsistent; break;
        case TheoryCheckResult::Kind::Conflict:
            ++modelCheckConflict;
            if (conflictSize > 0) {
                if (conflictMinSize < 0 || conflictSize < conflictMinSize) conflictMinSize = conflictSize;
                if (conflictSize > conflictMaxSize) conflictMaxSize = conflictSize;
                conflictTotalSize += conflictSize;
            }
            break;
        case TheoryCheckResult::Kind::Lemma: ++modelCheckLemma; break;
        case TheoryCheckResult::Kind::Unknown: ++modelCheckUnknown; break;
    }
}

void TheorySearchStats::recordPropagateCheck(bool conflict, bool lemma, int conflictSize,
                                             std::chrono::microseconds dur) {
    ++propagateTheoryCheckCount;
    propagateCheckTotalUs += dur.count();
    if (conflict) {
        ++propagateConflictCount;
        if (conflictSize > 0) {
            if (propagateConflictMinSize < 0 || conflictSize < propagateConflictMinSize)
                propagateConflictMinSize = conflictSize;
            if (conflictSize > propagateConflictMaxSize)
                propagateConflictMaxSize = conflictSize;
            propagateConflictTotalSize += conflictSize;
        }
    } else if (lemma) {
        ++propagateLemmaCount;
    }
}

void TheorySearchStats::print(std::ostream& out) const {
    out << "\n========== Theory Search Statistics ==========\n";
    out << "modelCheck (Full effort):\n";
    out << "  calls=" << modelCheckCount;
    if (modelCheckCount > 0) {
        out << " avg_us=" << (modelCheckTotalUs / modelCheckCount);
    }
    out << "\n";
    out << "  consistent=" << modelCheckConsistent
        << " conflict=" << modelCheckConflict
        << " lemma=" << modelCheckLemma
        << " unknowns=" << modelCheckUnknown << "\n";
    if (modelCheckConflict > 0) {
        out << "  conflict_size min=" << conflictMinSize
            << " max=" << conflictMaxSize
            << " avg=" << std::fixed << std::setprecision(1)
            << (static_cast<double>(conflictTotalSize) / modelCheckConflict) << "\n";
    }

    out << "cb_propagate (Standard effort):\n";
    out << "  total_calls=" << propagateCallCount
        << " theory_checks=" << propagateTheoryCheckCount << "\n";
    if (propagateTheoryCheckCount > 0) {
        out << "  check_avg_us=" << (propagateCheckTotalUs / propagateTheoryCheckCount) << "\n";
    }
    out << "  early_conflict=" << propagateConflictCount
        << " early_lemma=" << propagateLemmaCount << "\n";
    if (propagateConflictCount > 0) {
        out << "  early_conflict_size min=" << propagateConflictMinSize
            << " max=" << propagateConflictMaxSize
            << " avg=" << std::fixed << std::setprecision(1)
            << (static_cast<double>(propagateConflictTotalSize) / propagateConflictCount) << "\n";
    }
    out << "==============================================\n";
}

CadicalTheoryPropagator::CadicalTheoryPropagator(
    TheoryAtomLookup& registry,
    TheoryPropagationCallbacks& tm,
    TheoryLemmaStorage& lemmaDb,
    CadicalBackend& backend
) : registry_(registry), tm_(tm), lemmaDb_(lemmaDb), backend_(backend) {}

void CadicalTheoryPropagator::setUnknownReasonSink(std::string* sink) {
    unknownReasonSink_ = sink;
}

static void writeReason(std::string* sink, const std::string& msg) {
    if (sink) *sink = msg;
}

void CadicalTheoryPropagator::notify_assignment(const std::vector<int>& lits) {
    for (int lit : lits) {
        SatVar var = static_cast<SatVar>(std::abs(lit));
        bool sign = lit > 0;
        varToLevel_[var] = currentLevel_;
        currentAssignment_[var] = sign;
        const auto* atom = registry_.findBySatVar(var);
        if (!atom) continue;
        tm_.assertTheoryLit(*atom, SatLit{var, sign}, currentLevel_);
    }
}

void CadicalTheoryPropagator::notify_new_decision_level() {
    ++currentLevel_;
}

void CadicalTheoryPropagator::notify_backtrack(size_t new_level) {
    currentLevel_ = static_cast<int>(new_level);
    tm_.backtrackToLevel(currentLevel_);
    for (auto it = varToLevel_.begin(); it != varToLevel_.end(); ) {
        if (it->second > static_cast<int>(new_level)) {
            currentAssignment_.erase(it->first);
            it = varToLevel_.erase(it);
        } else {
            ++it;
        }
    }
}

bool CadicalTheoryPropagator::cb_check_found_model(const std::vector<int>& model) {
    if (abortWithUnknown_) {
        terminateSolve();
        return false;
    }

    // Slow-path fuse: prevent infinite loops from buggy theory solvers
    if (stats_.modelCheckCount + 1 > MAX_MODEL_CHECKS) {
        writeReason(unknownReasonSink_, "SAT: theory modelCheck budget exceeded (>" + std::to_string(MAX_MODEL_CHECKS) + ")");
        abortWithUnknown_ = true;
        terminateSolve();
        return false;
    }

    assignmentView_.clear();
    for (int lit : model) {
        SatVar var = static_cast<SatVar>(std::abs(lit));
        assignmentView_.setVarValue(var, lit > 0);
    }
    tm_.setAssignmentView(&assignmentView_);

    NO_DBG << "[CaDiCaL] cb_check_found_model modelSize=" << model.size() << "\n";

    // --- DEBUG: print all theory literals in current model ---
    std::cerr << "[SAT-MODEL] theory lits in model:\n";
    for (int lit : model) {
        SatVar var = static_cast<SatVar>(std::abs(lit));
        bool sign = lit > 0;
        const auto* atom = registry_.findBySatVar(var);
        if (!atom) continue;
        std::cerr << "[SAT-MODEL]  var=" << var
                  << " sign=" << (sign ? "T" : "F")
                  << " theory=" << (int)atom->theory
                  << " expr=" << atom->exprId
                  << " lit=" << lit << "\n";
    }

    // Reset theory state to level 0 before rebuilding from current model.
    // Without this, stale assignments from previous model checks accumulate
    // in solver trails and cause malformed conflict clauses (explain returns
    // reason lits that are false in the current model).
    tm_.backtrackToLevel(0);

    // Re-assert all theory atoms from the current model so that
    // TheoryManager rebuilds solver state after backtrack clears it.
    // This must include *all* theory atoms (LRA, LIA, EUF, Combination),
    // not just Combination atoms, otherwise legacy single-theory paths
    // see an empty active state after backtrack.
    for (int lit : model) {
        SatVar var = static_cast<SatVar>(std::abs(lit));
        bool sign = lit > 0;
        const auto* atom = registry_.findBySatVar(var);
        if (!atom) continue;
        int level = 0;
        auto it = varToLevel_.find(var);
        if (it != varToLevel_.end()) level = it->second;
        tm_.assertTheoryLit(*atom, SatLit{var, sign}, level);
    }
    for (int lit : model) {
        SatVar var = static_cast<SatVar>(std::abs(lit));
        bool sign = lit > 0;
        NO_DBG << "  raw=" << lit << " var=" << var << " sign=" << (sign ? "T" : "F") << "\n";
    }

    auto t0 = std::chrono::steady_clock::now();
    auto tr = tm_.check(lemmaDb_, TheoryEffort::Full);
    auto t1 = std::chrono::steady_clock::now();
    auto dur = std::chrono::duration_cast<std::chrono::microseconds>(t1 - t0);
    stats_.modelCheckTotalUs += dur.count();

    // Clear assignment view to avoid stale pointer in cb_propagate
    tm_.setAssignmentView(nullptr);

    int conflictSize = (tr.conflictOpt && !tr.conflictOpt->clause.empty())
                           ? static_cast<int>(tr.conflictOpt->clause.size()) : 0;
    stats_.recordModelCheckResult(tr.kind, conflictSize);
#ifdef NLCOLVER_ENABLE_CASESTATS
    updateCaseStatsSearch();
#endif

    std::cerr << "[PROP] modelCheck=" << stats_.modelCheckCount << " result=" << (int)tr.kind;
    if (!tr.reason.empty()) std::cerr << " reason=" << tr.reason;
    std::cerr << " us=" << dur.count();
    std::cerr << "\n";

    if (tr.kind == TheoryCheckResult::Kind::Consistent) {
        return true;
    }

    if (tr.kind == TheoryCheckResult::Kind::Conflict) {
        if (tr.conflictOpt && !tr.conflictOpt->clause.empty()) {
            std::cerr << "[PROP] conflict clause = ";
            for (SatLit lit : tr.conflictOpt->clause) {
                std::cerr << (lit.sign ? "" : "-") << lit.var << " ";
            }
            std::cerr << "\n";

            if (!isClauseFalsifiedByCurrentModel(tr.conflictOpt->clause)) {
                std::cerr << "[PROP][BUG] malformed external conflict clause. "
                             "Rejecting it to avoid infinite modelCheck loop.\n";
                abortWithUnknown_ = true;
                terminateSolve();
                return false;
            }

            enqueuePendingClause(tr.conflictOpt->clause);
            return false;
        }
        abortWithUnknown_ = true;
        terminateSolve();
        return false;
    }

    if (tr.kind == TheoryCheckResult::Kind::Lemma) {
        if (tr.lemmaOpt && !tr.lemmaOpt->lits.empty()) {
            // Always return the clause, even if seen before.
            // The current model violates the theory; we must reject it.
            lemmaDb_.insertIfNew(*tr.lemmaOpt);
            enqueuePendingClause(*tr.lemmaOpt);
            return false;
        }
        abortWithUnknown_ = true;
        terminateSolve();
        return false;
    }

    // Unknown
    if (!tr.reason.empty()) {
        writeReason(unknownReasonSink_, tr.reason);
    } else {
        writeReason(unknownReasonSink_, "Theory: unknown (no reason provided)");
    }
    abortWithUnknown_ = true;
    terminateSolve();
    return false;
}

int CadicalTheoryPropagator::cb_propagate() {
    ++stats_.propagateCallCount;
    if (abortWithUnknown_ || hasPendingClause_) return 0;

    // Throttle: avoid calling theory check on every propagate step.
    // Standard-effort LP checks are expensive; only run them when the
    // partial assignment has grown by a threshold, or after backtrack.
    size_t currentSize = currentAssignment_.size();
    int threshold = std::max(3, static_cast<int>(currentSize) / 10);
    bool sizeGrewEnough = (currentSize >= lastCheckedAssignmentSize_ + static_cast<size_t>(threshold));
    bool backtrackHappened = (currentSize < lastCheckedAssignmentSize_);
    if (!sizeGrewEnough && !backtrackHappened) return 0;
    lastCheckedAssignmentSize_ = currentSize;

    // Build partial assignment view for defensive validation in TheoryManager
    partialAssignmentView_.clear();
    for (const auto& [var, sign] : currentAssignment_) {
        partialAssignmentView_.setVarValue(var, sign);
    }
    tm_.setAssignmentView(&partialAssignmentView_);

    auto t0 = std::chrono::steady_clock::now();
    auto tr = tm_.check(lemmaDb_, TheoryEffort::Standard);
    auto t1 = std::chrono::steady_clock::now();
    auto dur = std::chrono::duration_cast<std::chrono::microseconds>(t1 - t0);

    // Clear assignment view to avoid stale pointer
    tm_.setAssignmentView(nullptr);

    int conflictSize = (tr.conflictOpt && !tr.conflictOpt->clause.empty())
                           ? static_cast<int>(tr.conflictOpt->clause.size()) : 0;
    bool isConflict = (tr.kind == TheoryCheckResult::Kind::Conflict);
    bool isLemma = (tr.kind == TheoryCheckResult::Kind::Lemma);
    stats_.recordPropagateCheck(isConflict, isLemma, conflictSize, dur);
#ifdef NLCOLVER_ENABLE_CASESTATS
    updateCaseStatsSearch();
    if (!dumpStatsBasePath_.empty()) {
        heartbeatWriter_.maybeWrite(*caseStats_, dumpStatsBasePath_);
    }
#endif

    if (isConflict) {
        if (tr.conflictOpt && !tr.conflictOpt->clause.empty()) {
            auto& clause = tr.conflictOpt->clause;
            // Safety: partial-assignment conflicts are only sound if every
            // literal in the clause is currently assigned.  If a theory solver
            // (e.g. NIA) includes auxiliary/unobserved literals, the partial
            // assignment is incomplete and the conflict may be spurious.
            bool allAssigned = true;
            for (SatLit lit : clause) {
                if (currentAssignment_.find(lit.var) == currentAssignment_.end()) {
                    allAssigned = false;
                    break;
                }
            }
            if (!allAssigned) {
                std::cerr << "[PROP] cb_propagate skip conflict with unassigned literals ("
                          << clause.size() << " lits)\n";
                return 0;
            }
            std::cerr << "[PROP] cb_propagate conflict clause = ";
            for (SatLit lit : clause) {
                std::cerr << (lit.sign ? "" : "-") << lit.var << " ";
            }
            std::cerr << " us=" << dur.count() << "\n";
            enqueuePendingClause(clause);
            return 0;
        }
        // Empty conflict clause is a bug; abort to avoid infinite loop
        abortWithUnknown_ = true;
        terminateSolve();
        return 0;
    }

    // NOTE: Lemmas from partial assignments (e.g. NIA branch lemmas) can
    // be based on incomplete information and may prune valid SAT branches.
    // Only propagate lemmas from complete model checks (cb_check_found_model).
    // Early conflicts are still returned because they are sound pruning.
    (void)isLemma;

    return 0;
}

bool CadicalTheoryPropagator::cb_has_external_clause(bool& is_forgettable) {
    is_forgettable = false;
    // If current clause exhausted, mark installed and pop
    while (hasPendingClause_ && currentPendingClausePos_ >= currentPendingClause_.size()) {
        if (!currentPendingClause_.empty()) {
            lemmaDb_.markInstalled(TheoryLemma{currentPendingClause_});
        }
        pendingClauses_.pop_front();
        if (pendingClauses_.empty()) {
            hasPendingClause_ = false;
            currentPendingClause_.clear();
            currentPendingClausePos_ = 0;
        } else {
            currentPendingClause_ = pendingClauses_.front();
            currentPendingClausePos_ = 0;
        }
    }
    return hasPendingClause_;
}

int CadicalTheoryPropagator::cb_add_external_clause_lit() {
    if (!hasPendingClause_) return 0;
    if (currentPendingClausePos_ >= currentPendingClause_.size()) {
        // Mark installed before moving to next
        if (!currentPendingClause_.empty()) {
            lemmaDb_.markInstalled(TheoryLemma{currentPendingClause_});
        }
        // Move to next pending clause
        pendingClauses_.pop_front();
        if (pendingClauses_.empty()) {
            hasPendingClause_ = false;
            currentPendingClause_.clear();
            currentPendingClausePos_ = 0;
            return 0;
        }
        currentPendingClause_ = pendingClauses_.front();
        currentPendingClausePos_ = 0;
    }
    SatLit lit = currentPendingClause_[currentPendingClausePos_++];
    return lit.sign ? static_cast<int>(lit.var) : -static_cast<int>(lit.var);
}

void CadicalTheoryPropagator::enqueuePendingClause(const std::vector<SatLit>& lits) {
    if (lits.empty()) return;
    pendingClauses_.push_back(lits);
    if (!hasPendingClause_) {
        hasPendingClause_ = true;
        currentPendingClause_ = lits;
        currentPendingClausePos_ = 0;
    }
    std::cerr << "[PROP] enqueuePendingClause: ";
    for (SatLit lit : lits) {
        std::cerr << (lit.sign ? "" : "-") << lit.var << " ";
    }
    std::cerr << "(queue_size=" << pendingClauses_.size() << ")\n";
}

void CadicalTheoryPropagator::enqueuePendingClause(const TheoryLemma& lemma) {
    enqueuePendingClause(lemma.lits);
}

void CadicalTheoryPropagator::terminateSolve() {
    backend_.requestTerminate();
}

#ifdef NLCOLVER_ENABLE_CASESTATS
void CadicalTheoryPropagator::updateCaseStatsSearch() {
    if (!caseStats_) return;
    caseStats_->search.modelCheckCalls = stats_.modelCheckCount;
    caseStats_->search.modelCheckConflicts = stats_.modelCheckConflict;
    caseStats_->search.modelCheckLemmas = stats_.modelCheckLemma;
    caseStats_->search.modelCheckUnknowns = stats_.modelCheckUnknown;

    // Combine model-check and propagate conflict sizes for overall stats
    int totalConflicts = stats_.modelCheckConflict + stats_.propagateConflictCount;
    long long totalConflictSize = stats_.conflictTotalSize + stats_.propagateConflictTotalSize;
    caseStats_->search.conflictMinSize = stats_.conflictMinSize;
    if (stats_.propagateConflictCount > 0) {
        if (caseStats_->search.conflictMinSize < 0 ||
            stats_.propagateConflictMinSize < caseStats_->search.conflictMinSize) {
            caseStats_->search.conflictMinSize = stats_.propagateConflictMinSize;
        }
    }
    caseStats_->search.conflictMaxSize = std::max(stats_.conflictMaxSize, stats_.propagateConflictMaxSize);
    if (totalConflicts > 0) {
        caseStats_->search.conflictAvgSize = static_cast<double>(totalConflictSize) / totalConflicts;
    }
    caseStats_->search.propagateCalls = stats_.propagateCallCount;
    caseStats_->search.propagateTheoryChecks = stats_.propagateTheoryCheckCount;
    caseStats_->search.propagateConflicts = stats_.propagateConflictCount;
    caseStats_->search.propagateLemmas = stats_.propagateLemmaCount;
}
#endif

bool CadicalTheoryPropagator::isClauseFalsifiedByCurrentModel(const std::vector<SatLit>& clause) const {
    bool ok = true;
    for (SatLit lit : clause) {
        LitValue v = assignmentView_.value(lit);
        if (v != LitValue::False) {
            ok = false;
            std::cerr << "[PROP][BAD CLAUSE] lit not false under model: "
                      << (lit.sign ? "" : "-") << lit.var
                      << " value=" << (v == LitValue::True ? "True" : "Unknown")
                      << "\n";
        }
    }
    return ok;
}

} // namespace nlcolver
