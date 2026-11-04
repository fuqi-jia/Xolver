#pragma once

#include "ir/NativeTerms.h"

#include <span>
#include <unordered_map>
#include <vector>

namespace xolver {

struct RequiredFact {
    ExprId expression;
    bool positive;
};

// Extract facts entailed by asserted roots without choosing Boolean branches.
// Negated implication requires its antecedents and negates its consequent;
// positive conjunction and negative disjunction require every child. Shared
// nodes are visited once per polarity, so contradictory requirements survive.
inline std::vector<RequiredFact> requiredFacts(
    const NativeTerms& terms, std::span<const ExprId> roots) {
    std::vector<RequiredFact> pending;
    for (size_t i = roots.size(); i > 0; --i) pending.push_back({roots[i - 1], true});
    std::unordered_map<ExprId, unsigned> visited;
    std::vector<RequiredFact> facts;
    while (!pending.empty()) {
        const auto fact = pending.back();
        pending.pop_back();
        const unsigned mask = fact.positive ? 1u : 2u;
        if (visited[fact.expression] & mask) continue;
        visited[fact.expression] |= mask;
        const auto node = terms.get(fact.expression);
        if (node.kind == Kind::Not && node.children.size() == 1) {
            pending.push_back({node.children[0], !fact.positive});
        } else if ((fact.positive && node.kind == Kind::And) ||
                   (!fact.positive && node.kind == Kind::Or)) {
            for (size_t i = node.children.size(); i > 0; --i)
                pending.push_back({node.children[i - 1], fact.positive});
        } else if (!fact.positive && node.kind == Kind::Implies && node.children.size() >= 2) {
            pending.push_back({node.children.back(), false});
            for (size_t i = node.children.size() - 1; i > 0; --i)
                pending.push_back({node.children[i - 1], true});
        } else {
            facts.push_back(fact);
        }
    }
    return facts;
}

} // namespace xolver
