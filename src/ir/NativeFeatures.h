#pragma once
#include <memory>
#include <vector>

namespace SOMTParser { class DAGNode; }
namespace xolver {
// Native syntax facts only. These do not select an application or give heap
// semantics to arrays, pointers, symbols or ordinary recursive equations.
struct NativeFeatures {
    bool quantified = false;
    bool spatial = false;
    bool real = false;
    bool integer = false;
    bool integerVariable = false;
    bool bitvector = false;
    bool otherSort = false;
    bool function = false;
};
NativeFeatures nativeFeatures(const std::vector<std::shared_ptr<SOMTParser::DAGNode>>&);
} // namespace xolver
