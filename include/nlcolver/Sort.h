#pragma once

#include <cstdint>

namespace nlcolver {

/**
 * Opaque handle for a solver sort.
 * Internally wraps a SortId (0 = null).
 */
class Sort {
public:
    Sort() = default;
    explicit Sort(uint32_t id) : id_(id) {}

    uint32_t id() const { return id_; }
    bool isNull() const { return id_ == 0; }

    bool operator==(const Sort& o) const { return id_ == o.id_; }
    bool operator!=(const Sort& o) const { return id_ != o.id_; }

private:
    uint32_t id_ = 0;
};

} // namespace nlcolver
