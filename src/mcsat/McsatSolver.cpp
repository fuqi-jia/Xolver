#include "mcsat/McsatSolver.h"

namespace nlcolver {

McsatSolver::McsatSolver() = default;

void McsatSolver::push() {}
void McsatSolver::pop(uint32_t) {}
void McsatSolver::reset() {}

void McsatSolver::assertLit(const TheoryAtom&, bool, const CoreIr&) {
    // TODO: add to theory trail
}

TheoryCheckResult McsatSolver::check(const CoreIr&) {
    // TODO: integrate with local search advisor and theory propagation
    return TheoryCheckResult::unknown();
}

void McsatSolver::setAdvisor(std::shared_ptr<LocalSearchAdvisor> advisor) {
    advisor_ = std::move(advisor);
}

} // namespace nlcolver
