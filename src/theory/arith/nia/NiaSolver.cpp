#include "theory/arith/nia/NiaSolver.h"

namespace nlcolver {

NiaSolver::NiaSolver() = default;

void NiaSolver::push() {}
void NiaSolver::pop(uint32_t) {}
void NiaSolver::reset() {}

void NiaSolver::assertLit(const TheoryAtom&, bool, const CoreIr&) {
    // TODO: dispatch to LIA / local search / bit-blaster
}

TheoryCheckResult NiaSolver::check(const CoreIr&) {
    // TODO: run hybrid portfolio
    return TheoryCheckResult::unknown();
}

void NiaSolver::setAdvisor(std::shared_ptr<LocalSearchAdvisor> advisor) {
    advisor_ = std::move(advisor);
}

} // namespace nlcolver
