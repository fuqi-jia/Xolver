#pragma once

#include <string>
#include <vector>
#include <queue>
#include <unordered_map>
#include <unordered_set>

namespace nlcolver {

class Worklist {
public:
    void push(size_t contractorId);
    size_t pop();
    bool empty() const;
    void pushAll(const std::vector<size_t>& ids);
    void clear();

private:
    std::queue<size_t> q_;
    std::unordered_set<size_t> inQueue_;
};

class WatcherMap {
public:
    void addWatcher(const std::string& var, size_t contractorId);
    std::vector<size_t> getWatchers(const std::string& var) const;
    void clear();

private:
    std::unordered_map<std::string, std::vector<size_t>> watchers_;
};

} // namespace nlcolver
