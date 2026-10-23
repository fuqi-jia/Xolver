#pragma once
#include "contracts/SolverAnswer.h"
#include "quantifiers/NativeInput.h"
#include "quantifiers/Resources.h"

namespace xolver::quantifiers::real {
// Quantified polynomial real arithmetic with arbitrary quantifier alternation.
SolverAnswer solve(const Roots&, Limits = {});
}
