#include "experimental/mcsat/McsatSolver.h"

namespace xolver {

McsatSolver::McsatSolver() = default;

void McsatSolver::push() {}
void McsatSolver::pop(uint32_t) {}
void McsatSolver::reset() {}

void McsatSolver::assertLit(const TheoryAtomRecord&, bool, int, SatLit) {
    // TODO: add to theory trail
}

void McsatSolver::backtrackToLevel(int) {
    // TODO: backtrack theory trail
}

TheoryCheckResult McsatSolver::check(TheoryLemmaStorage&, TheoryEffort) {
    // TODO: integrate with local search advisor and theory propagation
    return TheoryCheckResult::unknown();
}

void McsatSolver::setAdvisor(std::shared_ptr<LocalSearchAdvisor> advisor) {
    advisor_ = std::move(advisor);
}

} // namespace xolver
