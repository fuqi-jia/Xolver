#pragma once
#include "quantifiers/FiniteFormula.h"

namespace xolver::quantifiers::real {
// Quantified polynomial real arithmetic with arbitrary quantifier alternation.
SolverAnswer solve(const Roots&, Limits = {});
}
