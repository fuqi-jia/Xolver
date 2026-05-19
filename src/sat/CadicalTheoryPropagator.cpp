#include "sat/CadicalTheoryPropagator.h"

#ifdef NLCOLVER_HAS_CADICAL

#include "sat/CadicalBackend.h"
#include <cassert>
#include <iostream>

// Inline replacement for theory/core/DebugTrace.h to avoid sat/ -> theory/ include.
#define NO_DBG if (true) {} else std::cerr

namespace nlcolver {

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
            it = varToLevel_.erase(it);
        } else {
            ++it;
        }
    }
}

bool CadicalTheoryPropagator::cb_check_found_model(const std::vector<int>& model) {
    if (abortWithUnknown_) {
        terminateSolve();
        return true;
    }

    // Slow-path fuse: prevent infinite loops from buggy theory solvers
    if (++modelCheckCount_ > MAX_MODEL_CHECKS) {
        writeReason(unknownReasonSink_, "SAT: theory modelCheck budget exceeded (>" + std::to_string(MAX_MODEL_CHECKS) + ")");
        abortWithUnknown_ = true;
        terminateSolve();
        return true;
    }

    assignmentView_.clear();
    for (int lit : model) {
        SatVar var = static_cast<SatVar>(std::abs(lit));
        assignmentView_.setVarValue(var, lit > 0);
    }
    tm_.setAssignmentView(&assignmentView_);

    NO_DBG << "[CaDiCaL] cb_check_found_model modelSize=" << model.size() << "\n";

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

    auto tr = tm_.check(lemmaDb_, TheoryEffort::Full);
    std::cerr << "[PROP] modelCheck=" << modelCheckCount_ << " result=" << (int)tr.kind;
    if (!tr.reason.empty()) std::cerr << " reason=" << tr.reason;
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

            setPendingClause(tr.conflictOpt->clause);
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
            setPendingClause(*tr.lemmaOpt);
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

bool CadicalTheoryPropagator::cb_has_external_clause(bool& is_forgettable) {
    is_forgettable = false;
    return hasPendingClause_;
}

int CadicalTheoryPropagator::cb_add_external_clause_lit() {
    if (!hasPendingClause_) return 0;
    if (pendingClausePos_ == pendingClause_.size()) {
        hasPendingClause_ = false;
        pendingClause_.clear();
        pendingClausePos_ = 0;
        return 0;
    }
    SatLit lit = pendingClause_[pendingClausePos_++];
    return lit.sign ? static_cast<int>(lit.var) : -static_cast<int>(lit.var);
}

void CadicalTheoryPropagator::setPendingClause(const std::vector<SatLit>& lits) {
    pendingClause_ = lits;
    pendingClausePos_ = 0;
    hasPendingClause_ = true;
}

void CadicalTheoryPropagator::setPendingClause(const TheoryLemma& lemma) {
    setPendingClause(lemma.lits);
}

void CadicalTheoryPropagator::terminateSolve() {
    backend_.requestTerminate();
}

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

#endif // NLCOLVER_HAS_CADICAL
