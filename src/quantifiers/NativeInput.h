#pragma once
#include <memory>
#include <vector>

namespace SOMTParser { class DAGNode; }
namespace xolver::quantifiers {
using Roots = std::vector<std::shared_ptr<SOMTParser::DAGNode>>;
}
