#pragma once

#include <optional>
#include <cstddef>
#include <type_traits>
#include <utility>
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

// Theory-independent traversal of a finite sequence of candidate choices.
// candidates(depth) observes the propagated prefix. push(depth, value) opens a
// local choice and returns its feasibility; pop(depth) must be non-throwing and
// undo even a rejected/partially constructed choice. Every attempted push gets
// a matching pop, including on success or an exception. The theory owns its
// resource allocation, propagation, endpoint admissibility and final checker.
template <typename Candidates, typename Push, typename Pop, typename Complete>
auto searchBoundaryCandidates(size_t count, Candidates&& candidates, Push&& push,
                              Pop&& pop, Complete&& complete)
    -> std::invoke_result_t<Complete> {
    using Values = std::invoke_result_t<Candidates, size_t>;
    struct Frame { Values values; size_t next = 0; };
    std::vector<Frame> frames;
    size_t active = 0;
    auto unwind = [&]() { while (active) pop(--active); };
    try {
        for (;;) {
            if (active == count) {
                if (auto result = complete()) {
                    unwind();
                    return result;
                }
                if (!active) break;
                pop(--active);
                continue;
            }
            if (frames.size() == active) frames.push_back({candidates(active)});
            auto& frame = frames[active];
            if (frame.next == frame.values.size()) {
                frames.pop_back();
                if (!active) break;
                pop(--active);
                continue;
            }
            const auto value = frame.values[frame.next++];
            const size_t depth = active++;
            if (!push(depth, value)) pop(--active);
        }
    } catch (...) {
        unwind();
        throw;
    }
    return {};
}

} // namespace xolver
