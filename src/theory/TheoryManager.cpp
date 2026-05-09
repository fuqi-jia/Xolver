#include "theory/TheoryManager.h"

namespace nlcolver {

void TheoryManager::registerSolver(std::unique_ptr<TheorySolver> solver) {
    solvers_.push_back(std::move(solver));
}

void TheoryManager::push() {
    for (auto& s : solvers_) s->push();
}

void TheoryManager::pop(uint32_t n) {
    for (auto& s : solvers_) s->pop(n);
}

void TheoryManager::reset() {
    for (auto& s : solvers_) s->reset();
}

TheoryCheckResult TheoryManager::check(const CoreIr& ir,
                                       const std::vector<Atomizer::AtomRecord>& atoms,
                                       const SatSolver& sat) {
    if (solvers_.empty()) return TheoryCheckResult::consistent();

    for (auto& solver : solvers_) {
        solver->reset();

        // Feed theory literals to the solver based on SAT assignment.
        // Assert BOTH true and false literals.
        for (const auto& atom : atoms) {
            if (!atom.isTheory) continue;
            bool val = sat.value(atom.var);
            solver->assertLit({atom.var, atom.expr}, val, ir);
        }

        auto tr = solver->check(ir);
        if (tr.kind != TheoryCheckResult::Kind::Consistent) {
            return tr;
        }
    }

    return TheoryCheckResult::consistent();
}

} // namespace nlcolver
