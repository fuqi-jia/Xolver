#pragma once
#include "contracts/DecisionOracle.h"
#include "quantifiers/Resources.h"
namespace xolver::applications::smt::finite {
// Finite extensional arrays and Ackermann constraints for ground UF applications.
SolverAnswer solve(const NativeAssertions&, quantifiers::Limits = {});
}
