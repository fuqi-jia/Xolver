#pragma once
#include "contracts/SolverAnswer.h"
#include "contracts/IntegerArithmetic.h"

namespace xolver::applications::satisfiability::smt::lia {
// Quantified integer arithmetic. Owns result adaptation; shares elimination
// with other solver applications without invoking the SV/PA entry point.
SolverAnswer solve(const std::vector<std::shared_ptr<SOMTParser::DAGNode>>&,
             pa::Limits = {}, pa::EvidenceRequest = {});
} // namespace xolver::applications::satisfiability::smt::lia
