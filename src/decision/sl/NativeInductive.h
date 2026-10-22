#pragma once
#include "decision/sl/NativeSeparation.h"

namespace xolver::sl {
// Explicit SL least-fixed-point semantics. A generic SMT define-fun-rec
// declaration is not sufficient to select this interpretation.
struct InductiveDefinition {
    std::shared_ptr<SOMTParser::DAGNode> symbol;
    std::shared_ptr<SOMTParser::DAGNode> body;
    std::vector<std::shared_ptr<SOMTParser::DAGNode>> parameters;
};
NativeDecision decideInductiveNative(
    const std::shared_ptr<SOMTParser::Sort>& location,
    const std::shared_ptr<SOMTParser::Sort>& data,
    const std::vector<std::shared_ptr<SOMTParser::DAGNode>>& assertions,
    const std::vector<std::shared_ptr<SOMTParser::DAGNode>>& declarations,
    const std::vector<InductiveDefinition>& definitions, Limits = {});
} // namespace xolver::sl
