#pragma once
#include "contracts/SolverAnswer.h"
#include "contracts/IntegerArithmetic.h"
#include "quantifiers/Resources.h"

namespace xolver::applications::satisfiability::smt {
// SMT arithmetic certificate requests also pass here, including ground inputs.
// No fallback to a quantifier-free builder or to an SV application is allowed.
SolverAnswer solveFirstOrder(const std::vector<std::shared_ptr<SOMTParser::DAGNode>>&,
                       pa::Limits = {}, pa::EvidenceRequest = {}, quantifiers::Limits = {});
} // namespace xolver::applications::satisfiability::smt
