#pragma once

#include <cstdint>
#include <string>
#include <unordered_map>
#include <map>
#include <optional>

namespace xolver {

// The SMT heap interpretation. Integer values are canonical decimal strings;
// nil is an interpreted value, and need not be integer zero.
struct HeapModel {
    std::string locationSort;
    std::string dataSort;
    std::string nil;
    std::map<std::string, std::string> cells;
};

/**
 * Model: stores variable assignments from a satisfying query.
 */
class Model {
public:
    bool isEmpty() const { return values_.empty() && !heap_; }

    const std::optional<HeapModel>& heap() const { return heap_; }
    void setHeap(HeapModel heap) { heap_ = std::move(heap); }

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
    std::optional<HeapModel> heap_;
};

} // namespace xolver
