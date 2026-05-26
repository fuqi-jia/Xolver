#include "theory/arith/ArithSolverBase.h"
#include "theory/arith/Reasoner.h"
#include <cassert>
#include <cstdlib>
#include <iostream>

namespace zolver {

ArithSolverBase::ArithSolverBase() = default;
ArithSolverBase::~ArithSolverBase() = default;

TheoryCheckResult ArithSolverBase::check(TheoryLemmaStorage& lemmaDb,
                                         TheoryEffort effort) {
    return runReasonerPipeline(lemmaDb, effort);
}

std::vector<std::string> ArithSolverBase::reasonerNames() const {
    std::vector<std::string> names;
    names.reserve(reasoners_.size());
    for (const auto& r : reasoners_) names.push_back(r->name());
    return names;
}

TheoryCheckResult ArithSolverBase::runReasonerPipeline(TheoryLemmaStorage& lemmaDb,
                                                       TheoryEffort effort) {
    if (hasPending()) return drainPending();
    for (auto& r : reasoners_) {
        if (!r->runsAt(effort)) continue;
#ifndef NDEBUG
        size_t trailBefore = state_.trail.size();
#endif
        auto res = r->run(lemmaDb, effort);
        // Reasoners must not mutate the shared trail; only assertLit does.
        assert(state_.trail.size() == trailBefore && "Reasoner mutated trail");
        // nullopt = continue to next stage; a value = stop with that verdict
        // (Consistent here means "theory state is consistent, stop", NOT
        // "continue").
        if (res.has_value()) {
            static const bool stageDiag = std::getenv("ARITH_STAGE_DIAG") != nullptr;
            if (stageDiag && res->kind == TheoryCheckResult::Kind::Conflict) {
                std::cerr << "[STAGE-CONFLICT] stage=" << r->name()
                          << " size=" << (res->conflictOpt ? res->conflictOpt->clause.size() : 0)
                          << " lits=";
                if (res->conflictOpt) {
                    for (const auto& l : res->conflictOpt->clause)
                        std::cerr << (l.sign ? "" : "-") << l.var << " ";
                }
                std::cerr << "\n";
            }
            return std::move(*res);
        }
    }
    return TheoryCheckResult::consistent();
}

void ArithSolverBase::push() {
    ++state_.scopeLevel;
    onPush();
}

void ArithSolverBase::pop(uint32_t n) {
    if (state_.scopeLevel >= n) state_.scopeLevel -= n;
    else state_.scopeLevel = 0;
    onPop(n);
}

void ArithSolverBase::assertLit(const TheoryAtomRecord& atom, bool value,
                                int level, SatLit assertedLit) {
    // Dedup by satVar: replace an existing assignment for the same SAT
    // variable in place, else append. This reproduces the pre-refactor
    // assertLit body shared by IDL/RDL/NIA/NIRA/LIRA verbatim.
    for (auto& a : state_.trail) {
        if (a.atom.satVar == atom.satVar) {
            a = {level, assertedLit, atom, value};
            if (level > state_.currentLevel) state_.currentLevel = level;
            onAssertLit(atom, value, level, assertedLit);
            return;
        }
    }
    state_.trail.push_back({level, assertedLit, atom, value});
    if (level > state_.currentLevel) state_.currentLevel = level;
    onAssertLit(atom, value, level, assertedLit);
}

void ArithSolverBase::backtrackToLevel(int level) {
    auto it = std::remove_if(state_.trail.begin(), state_.trail.end(),
        [level](const ActiveAssignment& a) { return a.level > level; });
    state_.trail.erase(it, state_.trail.end());

    if (state_.pending && state_.pending->level > level) {
        state_.pending.reset();
    }
    state_.currentLevel = level;
    onBacktrack(level);
}

void ArithSolverBase::reset() {
    state_.trail.clear();
    state_.pending.reset();
    state_.currentLevel = 0;
    state_.scopeLevel = 0;
    onReset();
}

} // namespace zolver
