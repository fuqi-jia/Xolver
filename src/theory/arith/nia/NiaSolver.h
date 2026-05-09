#pragma once

#include "theory/TheorySolver.h"
#include "search/LocalSearchAdvisor.h"
#include <memory>

namespace nlcolver {

/**
 * NIA Solver: Nonlinear Integer Arithmetic.
 *
 * Stage I skeleton:
 *   - Hybrid approach: local search + LIA + branch-and-bound + bit-blasting
 *   - Modular pruning for divisibility constraints
 *   - Unknown with reason (when all sub-solvers give up)
 */
class NiaSolver : public TheorySolver {
public:
    NiaSolver();

    TheoryId id() const override { return TheoryId::NIA; }

    void push() override;
    void pop(uint32_t n) override;
    void assertLit(const TheoryAtom& atom, bool value, const CoreIr& ir) override;
    TheoryCheckResult check(const CoreIr& ir) override;
    void reset() override;

    void setAdvisor(std::shared_ptr<LocalSearchAdvisor> advisor);

private:
    std::shared_ptr<LocalSearchAdvisor> advisor_;
    // TODO: LIA wrapper, bit-blaster, modular arithmetic engine
};

} // namespace nlcolver
