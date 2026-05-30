#include "sat/CadicalTheoryPropagator.h"
#include "sat/CadicalBackend.h"
#include <cassert>
#include <iostream>
#include <iomanip>
#include <algorithm>
#include <vector>
#include <cstdlib>
#include <variant>

// Inline replacement for theory/core/DebugTrace.h to avoid sat/ -> theory/ include.
#define NO_DBG if (true) {} else std::cerr

namespace xolver {

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
) : registry_(registry), tm_(tm), lemmaDb_(lemmaDb), backend_(backend) {
    deferEarlyConflict_ = (std::getenv("XOLVER_SAT_DEFER_EARLY_CONFLICT") != nullptr);
}

void CadicalTheoryPropagator::setUnknownReasonSink(std::string* sink) {
    unknownReasonSink_ = sink;
}

static void writeReason(std::string* sink, const std::string& msg) {
    if (sink) *sink = msg;
}

void CadicalTheoryPropagator::notify_assignment(const std::vector<int>& lits) {
    // Decision-steering probe: the first literal assigned right after a new
    // decision level is CaDiCaL's decision literal. Bucket it theory vs boolean.
    if (expectDecisionLit_ && !lits.empty()) {
        expectDecisionLit_ = false;
        ++decisionLits_;
        SatVar dv = static_cast<SatVar>(std::abs(lits.front()));
        const auto* rec = registry_.findBySatVar(dv);
        if (rec && std::holds_alternative<LinearAtomPayload>(rec->payload)) {
            ++theoryAtomDecisions_;
        }
    }
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
    expectDecisionLit_ = true;  // next assignment's first lit is the decision
}

int CadicalTheoryPropagator::cb_decide() {
    ++decideCalls_;

    if (const char* pe = std::getenv("XOLVER_DECIDE_PROBE"); pe && *pe && *pe != '0') {
        static long long every = []() {
            const char* e = std::getenv("XOLVER_DECIDE_PROBE");
            long long n = e ? std::atoll(e) : 0;
            return n > 1 ? n : 2000;
        }();
        if (decideCalls_ % every == 0) {
            double pct = decisionLits_ ? 100.0 * static_cast<double>(theoryAtomDecisions_) / decisionLits_ : 0.0;
            std::cerr << "[DECIDE-PROBE] decisions=" << decideCalls_
                      << " steered=" << steeredDecisions_
                      << " unassignedProbes=" << dbgUnassignedProbes_
                      << " evalNull=" << dbgEvalNull_
                      << " observedDecisionLits=" << decisionLits_
                      << " theoryAtomDecisions=" << theoryAtomDecisions_
                      << " theoryAtomPct=" << pct << "%" << std::endl;
        }
    }

    // XOLVER_LRA_DECIDE: steer toward a theory-feasible region. Find an
    // unassigned bound atom (bounded cursor scan, O(K) per call, zero alloc),
    // evaluate it at the current theory model, and decide it at the satisfying
    // phase. Heuristic only: a decision is backtrackable and the verdict stays
    // theory-gated + model-validated, so a wrong guess only costs a backtrack.
    static const bool steer = []() {
        const char* e = std::getenv("XOLVER_LRA_DECIDE");
        return e && *e && *e != '0';
    }();
    if (steer) {
        if (!theoryAtomVarsBuilt_) {
            theoryAtomVars_ = registry_.linearAtomVars();
            theoryAtomVarsBuilt_ = true;
            if (std::getenv("XOLVER_DECIDE_PROBE"))
                std::cerr << "[DECIDE-STEER] theoryAtomVars=" << theoryAtomVars_.size() << std::endl;
        }
        const size_t n = theoryAtomVars_.size();
        if (n > 0) {
            const size_t kMaxProbe = n < 64 ? n : 64;
            for (size_t p = 0; p < kMaxProbe; ++p) {
                SatVar v = theoryAtomVars_[decideCursor_];
                decideCursor_ = (decideCursor_ + 1) % n;
                if (currentAssignment_.find(v) != currentAssignment_.end()) continue; // assigned
                ++dbgUnassignedProbes_;
                auto feasible = tm_.evalTheoryAtom(v);
                if (!feasible) { ++dbgEvalNull_; continue; }
                ++steeredDecisions_;
                int lit = static_cast<int>(v);
                return *feasible ? lit : -lit;  // decide at satisfying phase
            }
        }
        // fall through: no steerable unassigned atom found → let CaDiCaL decide
    }

    // Behavior-neutral: decline, let CaDiCaL decide (probe dump done at top).
    return 0;
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
    //
    // Re-assert each atom at its REAL SAT decision level (varToLevel_), but in
    // ASCENDING-LEVEL ORDER. The model vector is in trail/model order, whose
    // levels are non-monotonic; feeding that directly violates the theory
    // solvers' snapshot invariant (ensureSnapshotForLevel assumes non-decreasing
    // levels) and corrupts e-graph rollback. Sorting by level restores
    // monotonicity WHILE preserving the level<->trail correspondence, so the
    // rebuilt state matches the actual trail: a subsequent notify_backtrack(N)
    // rolls the theory back to exactly the level-N search state. Using a single
    // fixed level instead (an earlier workaround) broke that correspondence,
    // leaving model-check merges stale in continued search -> spurious
    // interface-disequality conflicts -> false UNSAT.
    auto levelOf = [this](SatVar v) -> int {
        auto it = varToLevel_.find(v);
        return it != varToLevel_.end() ? it->second : 0;
    };
    std::vector<int> ordered(model.begin(), model.end());
    std::stable_sort(ordered.begin(), ordered.end(), [&](int a, int b) {
        return levelOf(static_cast<SatVar>(std::abs(a)))
             < levelOf(static_cast<SatVar>(std::abs(b)));
    });
    for (int lit : ordered) {
        SatVar var = static_cast<SatVar>(std::abs(lit));
        bool sign = lit > 0;
        const auto* atom = registry_.findBySatVar(var);
        if (!atom) continue;
        tm_.assertTheoryLit(*atom, SatLit{var, sign}, levelOf(var));
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
#ifdef XOLVER_ENABLE_CASESTATS
    updateCaseStatsSearch();
#endif

    NO_DBG << "[PROP] modelCheck=" << stats_.modelCheckCount << " result=" << (int)tr.kind;
    if (!tr.reason.empty()) { NO_DBG << " reason=" << tr.reason; }
    NO_DBG << " us=" << dur.count();
    NO_DBG << "\n";

    if (tr.kind == TheoryCheckResult::Kind::Consistent) {
        return true;
    }

    if (tr.kind == TheoryCheckResult::Kind::Conflict) {
        if (tr.conflictOpt && !tr.conflictOpt->clause.empty()) {
            NO_DBG << "[PROP] conflict clause = ";
            for (SatLit lit : tr.conflictOpt->clause) {
                NO_DBG << (lit.sign ? "" : "-") << lit.var << " ";
            }
            NO_DBG << "\n";

            if (!isClauseFalsifiedByCurrentModel(tr.conflictOpt->clause)) {
                NO_DBG << "[PROP][BUG] malformed external conflict clause. "
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
#ifdef XOLVER_ENABLE_CASESTATS
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
                NO_DBG << "[PROP] cb_propagate skip conflict with unassigned literals ("
                          << clause.size() << " lits)\n";
                return 0;
            }
            // Soundness: an external conflict clause must be FALSIFIED — every
            // literal currently assigned to make it false. The clause stores
            // negated reasons (makeFalsifiedConflict), so each lit must be false
            // now: currentAssignment_[var] != lit.sign. If a lit is currently
            // TRUE, the "conflict" is not actually falsified — it rests on a
            // reason that no longer holds (e.g. an EUF explanation that walked a
            // STALE merge whose interface-equality literal has since been
            // unassigned/flipped — the xs_11_11/xs_15_15 false-UNSAT). Skipping a
            // non-falsified clause is always sound (it was never a valid conflict).
            bool falsified = true;
            for (SatLit lit : clause) {
                auto it = currentAssignment_.find(lit.var);
                if (it != currentAssignment_.end() && it->second == lit.sign) {
                    falsified = false;
                    break;
                }
            }
            if (!falsified) {
                if (std::getenv("XOLVER_WISA_DIAG"))
                    std::fprintf(stderr, "[PROP] SKIP non-falsified conflict (%zu lits) — stale reason\n",
                                 clause.size());
                NO_DBG << "[PROP] skip non-falsified conflict (" << clause.size() << " lits)\n";
                return 0;
            }
            // Soundness floor (XOLVER_SAT_DEFER_EARLY_CONFLICT): in combination
            // mode a Standard-effort theory conflict is UNVALIDATED (only pure
            // shared-eq conflicts are re-verified by conflictIsGenuine; a
            // mixed/theory conflict is trusted), so an unsound conflict can drive
            // a false UNSAT (e.g. QF_UFNIA 168-lit Standard conflict, never Full-
            // validated). Suppress it: let the search reach a complete model and
            // the authoritative Full-effort model check arbitrate. Sound — at
            // worst we lose early pruning; we never accept an unvalidated UNSAT.
            if (deferEarlyConflict_ && tm_.isCombinationMode()) {
                NO_DBG << "[PROP] defer Standard-effort early conflict ("
                       << clause.size() << " lits) to Full check\n";
                return 0;
            }
            NO_DBG << "[PROP] cb_propagate conflict clause = ";
            for (SatLit lit : clause) {
                NO_DBG << (lit.sign ? "" : "-") << lit.var << " ";
            }
            NO_DBG << " us=" << dur.count() << "\n";
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

    // Theory entailment propagation: pull each theory solver's entailed literals
    // (EUF e-propagation under XOLVER_EUF_PROP; LRA Farkas under XOLVER_LRA_PROP)
    // and enqueue them as reason-carrying clauses (¬reasons ∨ implied). Each is a
    // theory-VALID clause (the reasons entail `implied`), so adding it is sound
    // regardless of the current assignment; with the reasons currently true it
    // is unit and CaDiCaL propagates `implied`. Producers self-gate (return {}
    // when their flag is off / in combination), so the flag-off path is inert.
    //
    // Call-frequency throttle (XOLVER_THEORY_ENTAIL_PROP_EVERY, default 1 =
    // every call). Track 1 EUF e-prop is paired with EUF_PROP_BUDGET (inner
    // iteration cap) but on EUF-heavy corpora (QG-classification) the per-call
    // cost is still the bottleneck; throttling to every K cb_propagate calls
    // amortises it. Sound — propagation is a refinement, not a verdict driver.
    static const int entailPropEvery = []() {
        const char* v = std::getenv("XOLVER_THEORY_ENTAIL_PROP_EVERY");
        if (v && *v) { try { return std::max(1, std::atoi(v)); } catch (...) {} }
        return 1;
    }();
    if (!hasPendingClause_ &&
        (entailPropEvery == 1 ||
         (stats_.propagateCallCount % entailPropEvery == 0))) {
        auto props = tm_.takeEntailmentPropagations();
        for (auto& lem : props) {
            if (!lem.lits.empty()) enqueuePendingClause(lem.lits);
        }
    }

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
    NO_DBG << "[PROP] enqueuePendingClause: ";
    for (SatLit lit : lits) {
        NO_DBG << (lit.sign ? "" : "-") << lit.var << " ";
    }
    NO_DBG << "(queue_size=" << pendingClauses_.size() << ")\n";
}

void CadicalTheoryPropagator::enqueuePendingClause(const TheoryLemma& lemma) {
    enqueuePendingClause(lemma.lits);
}

void CadicalTheoryPropagator::terminateSolve() {
    backend_.requestTerminate();
}

#ifdef XOLVER_ENABLE_CASESTATS
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
            NO_DBG << "[PROP][BAD CLAUSE] lit not false under model: "
                      << (lit.sign ? "" : "-") << lit.var
                      << " value=" << (v == LitValue::True ? "True" : "Unknown")
                      << "\n";
        }
    }
    return ok;
}

} // namespace xolver
