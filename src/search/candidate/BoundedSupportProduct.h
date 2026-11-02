#pragma once

#include <algorithm>
#include <cstddef>
#include <utility>
#include <vector>

namespace xolver {

// Enumerate tuples with at most maxSupport non-default entries. Coordinate0
// changes fastest, matching an ordinary Cartesian odometer followed by a
// support filter. Prune prefixes before expanding their remaining product.
// visit receives borrowed domain indices and returns false to stop. The
// return value is true only on exhaustion. Cancellation from tick/visit
// propagates; domains and caller-owned state are never retained or modified.
template <typename Value, typename IsDefault, typename Visit, typename Tick>
bool enumerateBoundedSupportProduct(const std::vector<std::vector<Value>>& domains,
                                   size_t maxSupport, IsDefault&& isDefault,
                                   Visit&& visit, Tick&& tick) {
    const size_t count = domains.size();
    maxSupport = std::min(maxSupport, count);
    std::vector<std::vector<unsigned char>> costs;
    std::vector<size_t> mandatory(count + 1, 0);
    costs.reserve(count);
    for (size_t dimension = 0; dimension < count; ++dimension) {
        tick();
        if (domains[dimension].empty()) return true;
        std::vector<unsigned char> entries;
        bool hasDefault = false;
        entries.reserve(domains[dimension].size());
        for (const auto& value : domains[dimension]) {
            tick();
            const bool zero = isDefault(value);
            hasDefault |= zero;
            entries.push_back(zero ? 0 : 1);
        }
        mandatory[dimension + 1] = mandatory[dimension] + !hasDefault;
        costs.push_back(std::move(entries));
    }
    if (mandatory.back() > maxSupport) return true;
    std::vector<size_t> indices(count, 0), next(count, 0);
    size_t remaining = count, used = 0;
    for (;;) {
        tick();
        if (!remaining) {
            if (!visit(indices)) return false;
            if (!count) return true;
            remaining = 1;
            used -= costs[0][indices[0]];
            continue;
        }
        const size_t dimension = remaining - 1;
        if (next[dimension] == domains[dimension].size()) {
            next[dimension] = 0;
            if (remaining == count) return true;
            ++remaining;
            used -= costs[remaining - 1][indices[remaining - 1]];
            continue;
        }
        const size_t index = next[dimension]++;
        const size_t cost = costs[dimension][index];
        if (cost > maxSupport - used ||
            mandatory[dimension] > maxSupport - used - cost) continue;
        indices[dimension] = index;
        used += cost;
        --remaining;
    }
}

} // namespace xolver
