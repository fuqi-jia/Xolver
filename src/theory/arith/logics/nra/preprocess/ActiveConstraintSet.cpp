#include "theory/arith/logics/nra/preprocess/ActiveConstraintSet.h"
#include <algorithm>

namespace xolver {

static uint32_t litKey(SatLit lit) {
    return (static_cast<uint32_t>(lit.var) << 1) | (lit.sign ? 0u : 1u);
}

void ActiveConstraintSet::push() {
    scopeStack_.push_back(entries_.size());
}

void ActiveConstraintSet::pop(uint32_t n) {
    for (uint32_t i = 0; i < n && !scopeStack_.empty(); ++i) {
        size_t targetSize = scopeStack_.back();
        scopeStack_.pop_back();
        // Remove entries above targetSize and update indices
        for (size_t j = targetSize; j < entries_.size(); ++j) {
            idIndex_.erase(entries_[j].id);
            litIndex_.erase(litKey(entries_[j].reason));
        }
        entries_.resize(targetSize);
    }
}

void ActiveConstraintSet::clear() {
    entries_.clear();
    scopeStack_.clear();
    idIndex_.clear();
    litIndex_.clear();
}

void ActiveConstraintSet::addConstraint(const ActiveConstraintEntry& entry) {
    size_t idx = entries_.size();
    entries_.push_back(entry);
    idIndex_[entry.id] = idx;
    litIndex_[litKey(entry.reason)] = idx;
}

void ActiveConstraintSet::removeConstraintsAboveLevel(int level) {
    auto it = std::remove_if(entries_.begin(), entries_.end(),
        [level](const auto& e) { return e.level > level; });
    for (auto jt = it; jt != entries_.end(); ++jt) {
        idIndex_.erase(jt->id);
        litIndex_.erase(litKey(jt->reason));
    }
    entries_.erase(it, entries_.end());
    // Rebuild indices
    idIndex_.clear();
    litIndex_.clear();
    for (size_t i = 0; i < entries_.size(); ++i) {
        idIndex_[entries_[i].id] = i;
        litIndex_[litKey(entries_[i].reason)] = i;
    }
}

const ActiveConstraintEntry* ActiveConstraintSet::find(ConstraintId id) const {
    auto it = idIndex_.find(id);
    if (it != idIndex_.end()) return &entries_[it->second];
    return nullptr;
}

const ActiveConstraintEntry* ActiveConstraintSet::findByLit(SatLit lit) const {
    auto it = litIndex_.find(litKey(lit));
    if (it != litIndex_.end()) return &entries_[it->second];
    return nullptr;
}

std::vector<PolyId> ActiveConstraintSet::activePolys() const {
    std::unordered_set<PolyId> seen;
    std::vector<PolyId> result;
    for (const auto& e : entries_) {
        if (seen.insert(e.poly).second) result.push_back(e.poly);
    }
    return result;
}

std::vector<AtomId> ActiveConstraintSet::activeAtoms() const {
    std::unordered_set<AtomId> seen;
    std::vector<AtomId> result;
    for (const auto& e : entries_) {
        if (e.atom != NullAtom && seen.insert(e.atom).second) result.push_back(e.atom);
    }
    return result;
}

std::vector<ActiveConstraintEntry> ActiveConstraintSet::equationalConstraints() const {
    std::vector<ActiveConstraintEntry> result;
    for (const auto& e : entries_) {
        if (e.rel == Relation::Eq && e.isEC) result.push_back(e);
    }
    return result;
}

} // namespace xolver
