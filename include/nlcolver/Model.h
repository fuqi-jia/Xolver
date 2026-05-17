#pragma once

#include <cstdint>
#include <string>
#include <unordered_map>

namespace nlcolver {

/**
 * Model: stores variable assignments from a satisfying query.
 */
class Model {
public:
    bool isEmpty() const { return values_.empty(); }

    void setValue(uint32_t varId, std::string value) {
        values_[varId] = std::move(value);
    }

    const std::string* getValue(uint32_t varId) const {
        auto it = values_.find(varId);
        if (it != values_.end()) return &it->second;
        return nullptr;
    }

    const std::unordered_map<uint32_t, std::string>& values() const {
        return values_;
    }

private:
    std::unordered_map<uint32_t, std::string> values_;
};

} // namespace nlcolver
