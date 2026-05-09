#pragma once

#include "theory/TheorySolver.h"
#include "sat/Atomizer.h"
#include <memory>
#include <vector>

namespace nlcolver {

/**
 * TheoryManager: owns and orchestrates theory solvers.
 */
class TheoryManager {
public:
    void registerSolver(std::unique_ptr<TheorySolver> solver);

    void push();
    void pop(uint32_t n);
    void reset();

    // Check all theory solvers under the current SAT model.
    TheoryCheckResult check(const CoreIr& ir,
                            const std::vector<Atomizer::AtomRecord>& atoms,
                            const SatSolver& sat);

private:
    std::vector<std::unique_ptr<TheorySolver>> solvers_;
};

} // namespace nlcolver
