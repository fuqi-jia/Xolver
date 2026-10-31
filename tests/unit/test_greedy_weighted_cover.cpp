#include <doctest/doctest.h>
#include "base/WorkBudget.h"
#include "search/candidate/WeightedGreedyCover.h"
#include <limits>
#include <random>
#include <string>

using namespace xolver;

namespace {
using Edges = std::vector<std::vector<std::pair<int, int>>>;

// Independent full rescanning reference, including its complete tie order.
std::optional<std::vector<int>> rescanCover(const Edges& edges, const std::set<int>& retained) {
    std::set<int> pinned;
    std::vector<int> result;
    for (;;) {
        std::map<int, std::size_t> scores;
        bool unfinished = false;
        for (const auto& edge : edges) {
            std::size_t degree = 0;
            for (const auto& [node, weight] : edge)
                if (!pinned.contains(node)) degree += weight;
            if (degree <= 1) continue;
            unfinished = true;
            for (const auto& [node, weight] : edge)
                if (weight && !pinned.contains(node) && !retained.contains(node)) scores[node] += weight;
        }
        if (scores.empty()) return unfinished ? std::nullopt : std::optional(result);
        auto best = scores.begin();
        for (auto it = scores.begin(); it != scores.end(); ++it)
            if (it->second > best->second) best = it;
        result.push_back(best->first);
        pinned.insert(best->first);
    }
}
} // namespace

TEST_CASE("weighted greedy cover: incremental choices match independent rescanning") {
    std::mt19937 random(4817);
    for (int trial = 0; trial < 600; ++trial) {
        Edges edges(random() % 30);
        std::set<int> retained;
        const int nodes = 1 + random() % 16;
        for (int node = 0; node < nodes; ++node)
            if (random() % 5 == 0) retained.insert(node);
        for (auto& edge : edges)
            for (unsigned i = 0, count = random() % 7; i < count; ++i)
                edge.emplace_back(random() % nodes, random() % 4);
        const auto expected = rescanCover(edges, retained);
        const auto actual = greedyWeightedCover(edges, retained, [] {});
        REQUIRE(actual == expected);
        if (!actual) continue;
        const std::set<int> chosen(actual->begin(), actual->end());
        for (const auto node : chosen) CHECK_FALSE(retained.contains(node));
        for (const auto& edge : edges) {
            int remaining = 0;
            for (const auto& [node, weight] : edge)
                if (!chosen.contains(node)) remaining += weight;
            CHECK(remaining <= 1);
        }
    }
}

TEST_CASE("weighted greedy cover: ordered string nodes and retained blocks") {
    using Strings = std::vector<std::vector<std::pair<std::string, int>>>;
    const Strings edges{{{"a", 1}, {"b", 1}}, {{"b", 1}, {"c", 1}}};
    const auto cover = greedyWeightedCover(edges, std::set<std::string>{"a"}, [] {});
    REQUIRE(cover);
    CHECK(*cover == std::vector<std::string>{"b"});
    CHECK_FALSE(greedyWeightedCover(edges, std::set<std::string>{"a", "b"}, [] {}));
    CHECK(greedyWeightedCover(Edges{}, std::set<int>{}, [] {})->empty());
    CHECK(greedyWeightedCover(Edges{{{1, 0}, {2, 1}}}, std::set<int>{2}, [] {})->empty());
}

TEST_CASE("weighted greedy cover: rejects negative weights and checked sum overflow") {
    CHECK_THROWS_AS(greedyWeightedCover(Edges{{{1, -1}}}, std::set<int>{}, [] {}),
                    std::invalid_argument);
    using LargeEdges = std::vector<std::vector<std::pair<int, std::size_t>>>;
    const auto max = std::numeric_limits<std::size_t>::max();
    CHECK_THROWS_AS(greedyWeightedCover(LargeEdges{{{1, max}, {1, 1}}}, std::set<int>{}, [] {}),
                    std::overflow_error);
    CHECK_THROWS_AS(greedyWeightedCover(LargeEdges{{{1, max}, {2, 1}}}, std::set<int>{}, [] {}),
                    std::overflow_error);
    CHECK_THROWS_AS(greedyWeightedCover(LargeEdges{{{1, max}}, {{1, max}}}, std::set<int>{}, [] {}),
                    std::overflow_error);
}

TEST_CASE("weighted greedy cover: cancellation preserves inputs and a fresh invocation") {
    const Edges edges{{{0, 1}, {1, 1}}, {{1, 2}, {2, 1}}};
    const auto original = edges;
    WorkBudget interrupted(2);
    CHECK_THROWS_AS(greedyWeightedCover(edges, std::set<int>{}, [&] { interrupted.tick(); }),
                    ResourceExhausted);
    CHECK(edges == original);
    CHECK(greedyWeightedCover(edges, std::set<int>{}, [] {}) == rescanCover(edges, {}));
}

TEST_CASE("weighted greedy cover: sparse independent edges fit a linear work allocation") {
    Edges edges;
    constexpr int count = 2000;
    for (int i = 0; i < count; ++i) edges.push_back({{2 * i, 1}, {2 * i + 1, 1}});
    WorkBudget work(20 * count);
    const auto cover = greedyWeightedCover(edges, std::set<int>{}, [&] { work.tick(); });
    REQUIRE(cover);
    REQUIRE(cover->size() == count);
    for (int i = 0; i < count; ++i) CHECK((*cover)[i] == 2 * i);
}
