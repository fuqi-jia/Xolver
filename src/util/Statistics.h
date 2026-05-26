#pragma once

#include <cstdint>
#include <string>
#include <unordered_map>

namespace zolver {

/**
 * Simple key-value statistics tracker.
 */
class Statistics {
public:
    void increment(const std::string& key, uint64_t delta = 1);
    void set(const std::string& key, uint64_t value);
    uint64_t get(const std::string& key) const;

    const std::unordered_map<std::string, uint64_t>& all() const { return data_; }

private:
    std::unordered_map<std::string, uint64_t> data_;
};

} // namespace zolver
