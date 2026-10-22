#pragma once

#include <cstdint>
#include <limits>

namespace xolver {

/**
 * Opaque handle for a solver sort.
 * Internally wraps a SortId (UINT32_MAX = null).
 */
class Sort {
public:
    Sort() = default;
    explicit Sort(uint32_t id, uint64_t context = 0) : id_(id), context_(context) {}

    uint32_t id() const { return id_; }
    uint64_t context() const { return context_; }
    bool isNull() const { return id_ == std::numeric_limits<uint32_t>::max(); }

    bool operator==(const Sort& o) const { return id_ == o.id_ && context_ == o.context_; }
    bool operator!=(const Sort& o) const { return !(*this == o); }

private:
    uint32_t id_ = std::numeric_limits<uint32_t>::max();
    uint64_t context_ = 0;
};

} // namespace xolver
