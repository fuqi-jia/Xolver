#pragma once
#include "contracts/SolverAnswer.h"
#include "quantifiers/Resources.h"
#include <vector>

namespace SOMTParser { class DAGNode; }
namespace xolver::quantifiers {
using Roots = std::vector<std::shared_ptr<SOMTParser::DAGNode>>;
// Native finite-domain compilation shares the Boolean connectives and binder
// scoping between QBF and QBV. Each binding receives independent Boolean bits.
SolverAnswer solveFinite(const Roots&, Limits, bool bitvectors);
namespace boolean { SolverAnswer solve(const Roots&, Limits = {}); }
namespace bitvector { SolverAnswer solve(const Roots&, Limits = {}); }
// Evaluate in a fixed interpretation. No free symbol is searched or reassigned.
// Unmentioned finite symbols use zero/false, matching model completion.
std::optional<std::string> finiteValue(const std::shared_ptr<SOMTParser::DAGNode>&,
                                     const TheoryModel&, Limits = {});
}
