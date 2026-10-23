#pragma once
#include "contracts/DecisionOracle.h"
#include "quantifiers/Resources.h"
namespace xolver::applications::smt::fp {
SolverAnswer solve(const NativeAssertions&, quantifiers::Limits = {});
}
