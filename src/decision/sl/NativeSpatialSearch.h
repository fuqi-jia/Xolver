#pragma once
#include "decision/sl/NativeSeparation.h"

namespace xolver::sl::detail {
// The native Boolean/PA heap backend; its input has no heap-dependent binders.
NativeDecision decideGroundNative(
    const std::shared_ptr<SOMTParser::Sort>&,
    const std::shared_ptr<SOMTParser::Sort>&,
    const std::vector<std::shared_ptr<SOMTParser::DAGNode>>&,
    const std::vector<std::shared_ptr<SOMTParser::DAGNode>>&,
    Limits);
bool hasSpatialBinders(const std::vector<std::shared_ptr<SOMTParser::DAGNode>>&);
NativeDecision searchSpatialNative(
    const std::shared_ptr<SOMTParser::Sort>&,
    const std::shared_ptr<SOMTParser::Sort>&,
    const std::vector<std::shared_ptr<SOMTParser::DAGNode>>&,
    const std::vector<std::shared_ptr<SOMTParser::DAGNode>>&,
    Limits);
std::shared_ptr<SOMTParser::DAGNode> fixedHeapFormula(
    const std::shared_ptr<SOMTParser::DAGNode>&, const HeapModel&, Limits);
} // namespace xolver::sl::detail
