#pragma once
#include "contracts/SolverAnswer.h"
#include <functional>
#include <memory>
#include <vector>
namespace SOMTParser {
class DAGNode;
}
namespace xolver {
using NativeAssertions = std::vector<std::shared_ptr<SOMTParser::DAGNode>>;
// Application composition injects a solver without a dependency between
// application families. Each invocation is an independent assertion snapshot.
using DecisionOracle = std::function<SolverAnswer(const NativeAssertions &)>;
} // namespace xolver
