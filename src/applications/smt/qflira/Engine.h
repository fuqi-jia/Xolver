#pragma once
#include "applications/smt/Solver.h"
namespace xolver::applications::smt {
std::optional<SolverAnswer> solveLinearArithmetic(const Problem &);
}
