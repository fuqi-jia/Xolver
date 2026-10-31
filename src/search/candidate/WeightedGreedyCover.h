#pragma once

#include <cstddef>
#include <limits>
#include <map>
#include <optional>
#include <set>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <vector>

namespace xolver {

// Choose nodes until every edge has remaining weight at most one, without
// choosing retained nodes. Scores sum a node's weight in unfinished edges;
// highest score wins, with ties resolved by the node's ordering. Duplicate
// incidences are added, and zero weights are ignored. An impossible retained
// block returns nullopt. Invalid weights and caller cancellation propagate.
// Only incident edges change after a choice; each edge retires once. Inputs
// remain untouched, including when tick() interrupts the computation.
template <typename Node, typename Weight, typename Tick>
std::optional<std::vector<Node>> greedyWeightedCover(
    const std::vector<std::vector<std::pair<Node, Weight>>>& edges,
    const std::set<Node>& retained, Tick&& tick) {
    static_assert(std::is_integral_v<Weight>);
    struct Edge {
        std::map<Node, std::size_t> weights;
        std::size_t degree = 0;
    };
    struct Vertex {
        std::vector<std::pair<std::size_t, std::size_t>> incidence;
        std::size_t score = 0;
        bool chosen = false;
    };
    struct RankOrder {
        bool operator()(const std::pair<std::size_t, Node>& a,
                        const std::pair<std::size_t, Node>& b) const {
            return a.first != b.first ? a.first > b.first : a.second < b.second;
        }
    };
    auto add = [](std::size_t& value, std::size_t amount) {
        if (amount > std::numeric_limits<std::size_t>::max() - value)
            throw std::overflow_error("greedy cover weight overflow");
        value += amount;
    };
    std::vector<Edge> normalized;
    std::map<Node, Vertex> vertices;
    std::size_t unfinished = 0;
    for (const auto& input : edges) {
        tick();
        Edge edge;
        for (const auto& [node, weight] : input) {
            tick();
            if (!std::in_range<std::size_t>(weight))
                throw std::invalid_argument("greedy cover requires nonnegative weights");
            if (!weight) continue;
            add(edge.weights[node], static_cast<std::size_t>(weight));
            add(edge.degree, static_cast<std::size_t>(weight));
        }
        if (edge.degree <= 1) continue;
        std::size_t retainedDegree = 0;
        for (const auto& [node, weight] : edge.weights) {
            tick();
            if (retained.contains(node)) add(retainedDegree, weight);
            else {
                auto& vertex = vertices[node];
                vertex.incidence.emplace_back(normalized.size(), weight);
                add(vertex.score, weight);
            }
        }
        if (retainedDegree > 1) return std::nullopt;
        normalized.push_back(std::move(edge));
        ++unfinished;
    }
    std::set<std::pair<std::size_t, Node>, RankOrder> ranking;
    for (const auto& [node, vertex] : vertices) {
        tick();
        ranking.emplace(vertex.score, node);
    }
    std::vector<Node> choices;
    while (!ranking.empty()) {
        tick();
        const auto node = ranking.begin()->second;
        ranking.erase(ranking.begin());
        auto& chosen = vertices.at(node);
        chosen.chosen = true;
        choices.push_back(node);
        for (const auto& [index, weight] : chosen.incidence) {
            tick();
            auto& edge = normalized[index];
            if (edge.degree <= 1) continue;
            edge.degree -= weight;
            if (edge.degree > 1) continue;
            --unfinished;
            for (const auto& [other, contribution] : edge.weights) {
                tick();
                const auto it = vertices.find(other);
                if (it == vertices.end() || it->second.chosen) continue;
                auto& vertex = it->second;
                ranking.erase({vertex.score, other});
                vertex.score -= contribution;
                if (vertex.score) ranking.emplace(vertex.score, other);
            }
        }
    }
    if (unfinished) return std::nullopt;
    return choices;
}

} // namespace xolver
