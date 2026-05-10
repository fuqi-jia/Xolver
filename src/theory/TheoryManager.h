#pragma once

#include "theory/TheorySolver.h"
#include <memory>
#include <vector>
#include <unordered_map>

namespace nlcolver {

class TheoryManager {
public:
    void registerSolver(std::unique_ptr<TheorySolver> solver);
    void clearSolvers();

    void assertTheoryLit(const TheoryAtomRecord& atom, SatLit assignedLit, int level);
    void backtrackToLevel(int level);
    TheoryCheckResult check(TheoryLemmaDatabase& lemmaDb);

private:
    std::vector<std::unique_ptr<TheorySolver>> solvers_;
    std::unordered_map<TheoryId, TheorySolver*> solverByTheory_;
};

} // namespace nlcolver
