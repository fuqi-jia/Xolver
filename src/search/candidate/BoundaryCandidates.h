#pragma once

#include <optional>
#include <vector>

namespace xolver {

// The theory supplies admissible endpoints; ordering and duplicate removal do
// not assume an arithmetic domain or any scaling rule.
template <typename Value>
std::vector<Value> boundaryCandidates(const std::optional<Value>& lower,
                                      const std::optional<Value>& upper) {
    std::vector<Value> result;
    if (upper) result.push_back(*upper);
    if (lower && (!upper || *lower != *upper)) result.push_back(*lower);
    return result;
}

} // namespace xolver
