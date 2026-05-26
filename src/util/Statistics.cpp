#include "util/Statistics.h"

namespace zolver {

void Statistics::increment(const std::string& key, uint64_t delta) {
    data_[key] += delta;
}

void Statistics::set(const std::string& key, uint64_t value) {
    data_[key] = value;
}

uint64_t Statistics::get(const std::string& key) const {
    auto it = data_.find(key);
    return it != data_.end() ? it->second : 0;
}

} // namespace zolver
