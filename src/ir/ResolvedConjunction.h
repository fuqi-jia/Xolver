#pragma once

#include "ir/NativeTerms.h"

#include <functional>
#include <optional>
#include <span>
#include <unordered_map>
#include <vector>

namespace xolver {

// Expand resolution edges and conjunctions without recursive stack growth.
// Conjunction is idempotent: shared subgraphs are visited once, in input order.
// A cycle invalidates the expansion; callers must retain the original formula.
// The resolver supplies a stable, one-step substitution or the unchanged id.
inline std::optional<std::vector<ExprId>> resolvedConjuncts(
    const NativeTerms& terms, std::span<const ExprId> roots,
    const std::function<ExprId(ExprId)>& resolve = {}) {
    struct Work {
        ExprId id;
        bool leaving;
    };
    enum class State { Active, Complete };
    std::unordered_map<ExprId, State> states;
    std::vector<Work> pending;
    for (size_t i = roots.size(); i > 0; --i)
        pending.push_back({roots[i - 1], false});
    std::vector<ExprId> atoms;
    while (!pending.empty()) {
        const auto [id, leaving] = pending.back();
        pending.pop_back();
        if (leaving) {
            states[id] = State::Complete;
            continue;
        }
        if (const auto seen = states.find(id); seen != states.end()) {
            if (seen->second == State::Active) return std::nullopt;
            continue;
        }
        states.emplace(id, State::Active);
        pending.push_back({id, true});
        const auto resolved = resolve ? resolve(id) : id;
        if (resolved != id) {
            pending.push_back({resolved, false});
            continue;
        }
        const auto node = terms.get(id);
        if (node.kind == Kind::And) {
            for (size_t i = node.children.size(); i > 0; --i)
                pending.push_back({node.children[i - 1], false});
        } else {
            atoms.push_back(id);
        }
    }
    return atoms;
}

} // namespace xolver
