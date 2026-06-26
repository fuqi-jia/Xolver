#include "experimental/mcsat/McsatSolver.h"
#include "theory/arith/logics/nra/backend/AlgebraBackend.h"  // complete AlgebraBackend for unique_ptr dtor

namespace xolver {

McsatSolver::McsatSolver() = default;
McsatSolver::~McsatSolver() = default;

void McsatSolver::setEngine(std::unique_ptr<mcsat::MCSatEngine> engine,
                            TheoryId tid) {
    engine_ = std::move(engine);
    theoryId_ = tid;
}

void McsatSolver::setAlgebra(std::unique_ptr<AlgebraBackend> algebra) {
    ownedAlgebra_ = std::move(algebra);
}

void McsatSolver::setAdvisor(std::shared_ptr<LocalSearchAdvisor> advisor) {
    advisor_ = std::move(advisor);
}

void McsatSolver::push() {
    ++currentLevel_;
}

void McsatSolver::pop(uint32_t n) {
    int target = currentLevel_ - static_cast<int>(n);
    if (target < 0) target = 0;
    backtrackToLevel(target);
    currentLevel_ = target;
}

void McsatSolver::reset() {
    trail_.clear();
    pendingConflict_.reset();
    pendingGiveUp_.reset();
    currentLevel_ = 0;
    if (engine_) engine_->reset();
}

void McsatSolver::assertLit(const TheoryAtomRecord& atom, bool value,
                            int level, SatLit reason) {
    // Mirror the SAT-side assertion onto the M-trail (as a Boolean
    // propagation justified by the SAT literal itself) AND notify the
    // engine. Sound: this entry only records the Boolean polarity, not
    // any theory value.
    SatLit lit{reason.var, reason.sign};
    trail_.pushBoolPropagation(lit, level, {reason});
    if (engine_) engine_->onAssertAtom(atom, value, level, reason);
}

void McsatSolver::backtrackToLevel(int level) {
    trail_.backtrackToLevel(level);
    pendingConflict_.reset();
    pendingGiveUp_.reset();
    if (engine_) engine_->onBacktrack(level);
    if (currentLevel_ > level) currentLevel_ = level;
}

bool McsatSolver::tryDecideOnce_() {
    if (!engine_) return false;
    VarId v = engine_->pickNextVar(trail_);
    if (v == NullVar) return false;
    mcsat::ValueChoice vc = engine_->pickValue(v, trail_);
    using K = mcsat::ValueChoice::Kind;
    switch (vc.kind) {
        case K::Found:
            trail_.pushTheoryDecision(v, std::move(vc.value), currentLevel_);
            return true;
        case K::Conflict: {
            std::vector<SatLit> clause =
                engine_->explainConflict(trail_, vc.blockingAtoms);
            // Sound floor: if the engine returned an empty explanation,
            // downgrade to Unknown rather than emit an empty (false) clause,
            // which would force a spurious UNSAT (§15.10 — every learned
            // clause must be theory-valid; an empty clause is not).
            if (clause.empty()) {
                pendingGiveUp_ = std::string{"NlsatEngine: empty explanation"};
            } else {
                TheoryConflict tc;
                tc.clause = std::move(clause);
                pendingConflict_ = std::move(tc);
            }
            return false;
        }
        case K::GiveUp:
            pendingGiveUp_ = std::move(vc.reason);
            return false;
    }
    return false;
}

TheoryCheckResult McsatSolver::check(TheoryLemmaStorage& /*lemmaDb*/,
                                     TheoryEffort /*effort*/) {
    if (!engine_) {
        return TheoryCheckResult::unknown("McsatSolver: no engine attached");
    }

    // Engine-side theory propagations first — record forced values that
    // arise from singleton feasible sets.
    auto props = engine_->propagate(trail_);
    for (auto& p : props) {
        trail_.pushTheoryPropagation(p.var, std::move(p.value),
                                     currentLevel_, std::move(p.reasons));
    }

    // Decide loop: pick a variable, choose a feasible value, push the
    // entry. Stop when the engine reports "all variables decided" or
    // signals a conflict.
    while (true) {
        if (pendingConflict_) {
            TheoryConflict tc = std::move(*pendingConflict_);
            pendingConflict_.reset();
            return TheoryCheckResult::mkConflict(std::move(tc));
        }
        if (pendingGiveUp_) {
            std::string why = std::move(*pendingGiveUp_);
            pendingGiveUp_.reset();
            // A GiveUp may carry a theory split lemma (e.g. an integrality split):
            // emit it so the SAT side branches, then re-enters check(). Returning
            // a lemma (not Unknown) is what drives the integer-NLSAT loop forward.
            auto lemmas = engine_->takeLemmas();
            if (!lemmas.empty())
                return TheoryCheckResult::mkLemma(std::move(lemmas.front()));
            return TheoryCheckResult::unknown(std::move(why));
        }
        if (!tryDecideOnce_()) {
            if (pendingConflict_ || pendingGiveUp_) continue;
            break;
        }
    }

    // Trail is fully assigned (engine-side) — validate against the
    // original assertions. Sound: returning Sat without engine_->
    // validateModel succeeding would violate invariant 1 of CLAUDE.md.
    TheorySolver::TheoryModel model;
    if (engine_->validateModel(trail_, model)) {
        return TheoryCheckResult::consistent();
    }
    return TheoryCheckResult::unknown("McsatSolver: validation failed");
}

} // namespace xolver
