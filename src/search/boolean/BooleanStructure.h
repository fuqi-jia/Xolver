#pragma once

#include "ir/NativeTerms.h"
#include <cstdint>
#include <span>
#include <unordered_set>
#include <utility>
#include <vector>

namespace xolver {

// Recognize Boolean alternatives without inspecting theory atoms. Negated Or
// and negated implication are conjunctions of literals after pushing Not down.
// This is structural portfolio routing, never a satisfiability conclusion.
inline bool hasBooleanAlternatives(const NativeTerms& terms, std::span<const ExprId> roots) {
    std::vector<std::pair<ExprId, bool>> pending;
    for (auto root : roots) pending.emplace_back(root, false);
    std::unordered_set<uint64_t> visited;
    while (!pending.empty()) {
        const auto [id, negative] = pending.back();
        pending.pop_back();
        if (!visited.insert(uint64_t(id) * 2 + negative).second) continue;
        const auto& term = terms.get(id);
        const auto& children = term.children;
        switch (term.kind) {
            case Kind::Not:
                if (children.size() != 1) return true;
                pending.emplace_back(children[0], !negative);
                break;
            case Kind::And:
            case Kind::Or:
                if (children.size() > 1 && (term.kind == Kind::Or) != negative) return true;
                for (auto child : children) pending.emplace_back(child, negative);
                break;
            case Kind::Implies:
                if (children.empty()) return true;
                if (!negative && children.size() > 1) return true;
                for (size_t i = 0; i < children.size(); ++i)
                    pending.emplace_back(children[i], i + 1 == children.size() ? negative : !negative);
                break;
            case Kind::Xor:
                if (children.size() > 1) return true;
                for (auto child : children) pending.emplace_back(child, negative);
                break;
            case Kind::Ite:
                return true;
            case Kind::Eq:
            case Kind::Distinct:
                if (children.size() > 1 && terms.get(children[0]).sort == terms.boolSortId()) return true;
                break;
            default:
                break; // Theory atoms and Boolean constants/variables are literals.
        }
    }
    return false;
}

} // namespace xolver
