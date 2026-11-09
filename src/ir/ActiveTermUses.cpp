#include "ir/ActiveTermUses.h"
#include <algorithm>
#include <cassert>

namespace xolver {

void ActiveTermUses::grow(ExprId id) {
    const auto size = static_cast<size_t>(id) + 1;
    if (references_.size() >= size) return;
    references_.resize(size, 0);
    indexed_.resize(size, false);
    parents_.resize(size);
    rootSlots_.resize(size);
}

void ActiveTermUses::retain(ExprId root) {
    std::vector<ExprId> pending{root};
    while (!pending.empty()) {
        const auto id = pending.back();
        pending.pop_back();
        ++work_;
        grow(id);
        if (references_[id]++ != 0) continue;
        const auto& node = ir_.get(id);
        if (!indexed_[id]) {
            indexed_[id] = true;
            if (node.kind == Kind::Variable)
                if (const auto* name = std::get_if<std::string>(&node.payload.value))
                    variables_[*name].push_back(id);
        }
        for (const auto child : node.children) {
            grow(child);
            parents_[child].insert(id);
            pending.push_back(child);
        }
    }
}

void ActiveTermUses::release(ExprId root) {
    std::vector<ExprId> pending{root};
    while (!pending.empty()) {
        const auto id = pending.back();
        pending.pop_back();
        ++work_;
        assert(references_[id] > 0);
        if (--references_[id] != 0) continue;
        for (const auto child : ir_.get(id).children) {
            parents_[child].erase(id);
            pending.push_back(child);
        }
    }
}

void ActiveTermUses::setRoot(size_t slot, ExprId root) {
    if (roots_.size() <= slot) roots_.resize(slot + 1, NullExpr);
    const auto old = roots_[slot];
    if (old == root) return;
    // Retain first: shared subtrees stay live while an assertion is replaced.
    if (root != NullExpr) {
        retain(root);
        rootSlots_[root].insert(slot);
    }
    roots_[slot] = root;
    if (old != NullExpr) {
        rootSlots_[old].erase(slot);
        release(old);
    }
}

ActiveTermUses::Closure ActiveTermUses::variableClosure(const std::string& name) {
    Closure result;
    const auto found = variables_.find(name);
    if (found == variables_.end()) return result;
    std::vector<ExprId> pending;
    for (const auto variable : found->second)
        if (references_[variable] != 0) pending.push_back(variable);
    while (!pending.empty()) {
        const auto id = pending.back();
        pending.pop_back();
        ++work_;
        if (!result.terms.insert(id).second) continue;
        for (const auto slot : rootSlots_[id]) result.roots.push_back(slot);
        for (const auto parent : parents_[id]) pending.push_back(parent);
    }
    std::sort(result.roots.begin(), result.roots.end());
    result.roots.erase(std::unique(result.roots.begin(), result.roots.end()), result.roots.end());
    return result;
}

} // namespace xolver
