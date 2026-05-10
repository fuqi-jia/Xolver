#include "theory/TheoryManager.h"

namespace nlcolver {

void TheoryManager::registerSolver(std::unique_ptr<TheorySolver> solver) {
    TheoryId id = solver->id();
    solvers_.push_back(std::move(solver));
    solverByTheory_[id] = solvers_.back().get();
}

void TheoryManager::clearSolvers() {
    solvers_.clear();
    solverByTheory_.clear();
}

void TheoryManager::assertTheoryLit(const TheoryAtomRecord& atom, SatLit assignedLit, int level) {
    auto it = solverByTheory_.find(atom.theory);
    if (it != solverByTheory_.end()) {
        it->second->assertLit(atom, assignedLit.sign, level, assignedLit);
    }
}

void TheoryManager::backtrackToLevel(int level) {
    for (auto& solver : solvers_) {
        solver->backtrackToLevel(level);
    }
}

TheoryCheckResult TheoryManager::check(TheoryLemmaDatabase& lemmaDb) {
    if (solvers_.empty()) return TheoryCheckResult::consistent();

    for (auto& solver : solvers_) {
        auto tr = solver->check(lemmaDb);
        if (tr.kind != TheoryCheckResult::Kind::Consistent) {
            return tr;
        }
    }
    return TheoryCheckResult::consistent();
}

} // namespace nlcolver
