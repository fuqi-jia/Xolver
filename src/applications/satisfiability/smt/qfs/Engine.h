#pragma once
#include "contracts/DecisionOracle.h"
#include "quantifiers/Resources.h"
namespace xolver::applications::satisfiability::smt::strings {
SolverAnswer solve(const NativeAssertions &, quantifiers::Limits = {});
}
