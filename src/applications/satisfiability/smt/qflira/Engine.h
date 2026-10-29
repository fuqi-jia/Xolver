#pragma once
#include "applications/satisfiability/smt/Solver.h"
namespace xolver::applications::satisfiability::smt {
std::optional<SolverAnswer> solveLinearArithmetic(const Problem &);
}
