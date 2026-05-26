#include "theory/arith/icp/Worklist.h"

namespace zolver {

void Worklist::push(size_t contractorId) {
    if (inQueue_.insert(contractorId).second) {
        q_.push(contractorId);
    }
}

size_t Worklist::pop() {
    size_t id = q_.front();
    q_.pop();
    inQueue_.erase(id);
    return id;
}

bool Worklist::empty() const {
    return q_.empty();
}

void Worklist::pushAll(const std::vector<size_t>& ids) {
    for (size_t id : ids) {
        push(id);
    }
}

void Worklist::clear() {
    while (!q_.empty()) q_.pop();
    inQueue_.clear();
}

void WatcherMap::addWatcher(const std::string& var, size_t contractorId) {
    watchers_[var].push_back(contractorId);
}

std::vector<size_t> WatcherMap::getWatchers(const std::string& var) const {
    auto it = watchers_.find(var);
    if (it == watchers_.end()) return {};
    return it->second;
}

void WatcherMap::clear() {
    watchers_.clear();
}

} // namespace zolver
