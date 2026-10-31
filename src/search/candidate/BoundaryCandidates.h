#pragma once

#include <optional>
#include <algorithm>
#include <cstddef>
#include <set>
#include <stdexcept>
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

template <typename Value>
struct CandidateChoices {
    std::vector<Value> values;
    // The CONTENT of this finite domain must remain valid when all listed
    // earlier choices stay fixed. Ordering may vary. Include the entire prefix
    // when a theory cannot explain how its propagated domain was generated.
    std::vector<size_t> dependencies;
};

struct CandidatePropagation {
    // nullopt accepts the choice. A conflict lists active choice depths whose
    // current values already make this branch infeasible; an empty conflict
    // rejects it independently of every choice.
    std::optional<std::vector<size_t>> conflict;
    static CandidatePropagation accept() { return {}; }
    static CandidatePropagation reject(std::vector<size_t> dependencies) {
        return {std::move(dependencies)};
    }
};

struct CandidateSearchStatistics {
    size_t propagationConflicts = 0, exhaustedDomains = 0;
    size_t backjumps = 0, skippedLevels = 0;
};

// Theory-independent finite candidate search with explained backjumping.
// candidates(depth) returns values AND their prefix dependencies. push opens a
// local choice and returns acceptance or an explained conflict; pop must undo
// even rejected/partially constructed choices without throwing. Every attempted
// push gets a matching pop, including on success or an exception. Domain
// exhaustion resolves rejected choices together with domain-generation reasons.
// A failed final checker conservatively depends on the entire prefix. Failure
// only exhausts these candidates; it proves nothing about an original theory.
template <typename Candidates, typename Push, typename Pop, typename Complete>
auto searchBoundaryCandidates(size_t count, Candidates&& candidates, Push&& push,
                              Pop&& pop, Complete&& complete,
                              CandidateSearchStatistics* statistics = nullptr)
    -> std::invoke_result_t<Complete> {
    using Choices = std::invoke_result_t<Candidates, size_t>;
    struct Frame {
        Choices choices;
        size_t next = 0;
        std::set<size_t> failures;
    };
    CandidateSearchStatistics local;
    auto& stats = statistics ? *statistics : local;
    stats = {};
    std::vector<Frame> frames;
    size_t active = 0;
    auto unwind = [&]() { while (active) pop(--active); };
    auto normalize = [](std::vector<size_t> dependencies, size_t limit) {
        std::sort(dependencies.begin(), dependencies.end());
        dependencies.erase(std::unique(dependencies.begin(), dependencies.end()), dependencies.end());
        if (!dependencies.empty() && dependencies.back() >= limit)
            throw std::invalid_argument("candidate explanation references an inactive choice");
        return dependencies;
    };
    auto reject = [&](std::vector<size_t> dependencies) {
        dependencies = normalize(std::move(dependencies), active);
        if (dependencies.empty()) {
            unwind();
            return false;
        }
        const auto target = dependencies.back();
        if (active > target + 1) {
            ++stats.backjumps;
            stats.skippedLevels += active - target - 1;
        }
        while (active > target) pop(--active);
        frames.resize(target + 1);
        dependencies.pop_back();
        frames[target].failures.insert(dependencies.begin(), dependencies.end());
        return true;
    };
    try {
        for (;;) {
            if (active == count) {
                if (auto result = complete()) {
                    unwind();
                    return result;
                }
                if (!active) break;
                std::vector<size_t> dependencies;
                for (size_t depth = 0; depth < active; ++depth) dependencies.push_back(depth);
                if (!reject(std::move(dependencies))) break;
                continue;
            }
            if (frames.size() == active) {
                auto choices = candidates(active);
                choices.dependencies = normalize(std::move(choices.dependencies), active);
                std::set<size_t> dependencies(choices.dependencies.begin(), choices.dependencies.end());
                frames.push_back({std::move(choices), 0, std::move(dependencies)});
            }
            auto& frame = frames[active];
            if (frame.next == frame.choices.values.size()) {
                ++stats.exhaustedDomains;
                std::vector<size_t> dependencies(frame.failures.begin(), frame.failures.end());
                frames.pop_back();
                if (!reject(std::move(dependencies))) break;
                continue;
            }
            const auto value = frame.choices.values[frame.next++];
            const size_t depth = active++;
            auto result = push(depth, value);
            if (result.conflict) {
                ++stats.propagationConflicts;
                if (!reject(std::move(*result.conflict))) break;
            }
        }
    } catch (...) {
        unwind();
        throw;
    }
    return {};
}

} // namespace xolver
