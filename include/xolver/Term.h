#pragma once

#include <cstdint>
#include <limits>

namespace xolver {

/**
 * Opaque handle for a solver term.
 * Internally wraps an ExprId (UINT32_MAX = null; zero is a valid term).
 */
class Term {
public:
    Term() = default;
    explicit Term(uint32_t id, uint64_t context = 0) : id_(id), context_(context) {}

    uint32_t id() const { return id_; }
    uint64_t context() const { return context_; }
    bool isNull() const { return id_ == std::numeric_limits<uint32_t>::max(); }

    bool operator==(const Term& o) const { return id_ == o.id_ && context_ == o.context_; }
    bool operator!=(const Term& o) const { return !(*this == o); }

private:
    uint32_t id_ = std::numeric_limits<uint32_t>::max();
    uint64_t context_ = 0;
};

} // namespace xolver
