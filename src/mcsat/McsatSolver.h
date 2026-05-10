#pragma once

#include "theory/TheorySolver.h"
#include "search/LocalSearchAdvisor.h"
#include <memory>

namespace nlcolver {

/**
 * MCSAT / NLSAT Solver.
 *
 * Stage H skeleton:
 *   - Theory trail: maintains assignments to theory variables
 *   - Value decisions: proposes theory values (from LocalSearchAdvisor)
 *   - Clause-level feasible set: tracks which theory values are still valid
 *   - Bridge between SAT decisions and theory propagation
 */
class McsatSolver : public TheorySolver {
public:
    McsatSolver();

    TheoryId id() const override { return TheoryId::NRA; }

    void push() override;
    void pop(uint32_t n) override;
    void assertLit(const TheoryAtomRecord& atom, bool value, int level, SatLit reason) override;
    void backtrackToLevel(int level) override;
    TheoryCheckResult check(TheoryLemmaDatabase& lemmaDb) override;
    void reset() override;

    // Set the local search advisor for proposal generation.
    void setAdvisor(std::shared_ptr<LocalSearchAdvisor> advisor);

private:
    std::shared_ptr<LocalSearchAdvisor> advisor_;
    // TODO: theory trail, value decisions, feasible sets
};

} // namespace nlcolver
