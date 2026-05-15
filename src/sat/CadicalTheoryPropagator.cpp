#include "sat/CadicalTheoryPropagator.h"

#ifdef NLCOLVER_HAS_CADICAL

#include "sat/CadicalBackend.h"
#include <cassert>
#include <iostream>

namespace nlcolver {

CadicalTheoryPropagator::CadicalTheoryPropagator(
    TheoryAtomRegistry& registry,
    TheoryManager& tm,
    TheoryLemmaDatabase& lemmaDb,
    CadicalBackend& backend
) : registry_(registry), tm_(tm), lemmaDb_(lemmaDb), backend_(backend) {}

void CadicalTheoryPropagator::notify_assignment(const std::vector<int>& lits) {
    for (int lit : lits) {
        SatVar var = static_cast<SatVar>(std::abs(lit));
        bool sign = lit > 0;
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
}

bool CadicalTheoryPropagator::cb_check_found_model(const std::vector<int>& model) {
    if (abortWithUnknown_) {
        terminateSolve();
        return true;
    }

    // Slow-path fuse: prevent infinite loops from buggy theory solvers
    if (++modelCheckCount_ > MAX_MODEL_CHECKS) {
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

    auto tr = tm_.check(lemmaDb_);
    std::cerr << "[PROP] check result=" << (int)tr.kind << "\n";

    if (tr.kind == TheoryCheckResult::Kind::Consistent) {
        return true;
    }

    if (tr.kind == TheoryCheckResult::Kind::Conflict) {
        if (tr.conflictOpt && !tr.conflictOpt->clause.empty()) {
            setPendingClause(tr.conflictOpt->clause);
            return false;
        }
        abortWithUnknown_ = true;
        terminateSolve();
        return true;
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
        return true;
    }

    // Unknown
    abortWithUnknown_ = true;
    terminateSolve();
    return true;
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

} // namespace nlcolver

#endif // NLCOLVER_HAS_CADICAL
