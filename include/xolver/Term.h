#pragma once

#include <cstdint>

namespace xolver {

/**
 * Opaque handle for a solver term.
 * Internally wraps an ExprId (0 = null).
 */
class Term {
public:
    Term() = default;
    explicit Term(uint32_t id) : id_(id) {}

    uint32_t id() const { return id_; }
    bool isNull() const { return id_ == 0; }

    bool operator==(const Term& o) const { return id_ == o.id_; }
    bool operator!=(const Term& o) const { return id_ != o.id_; }

private:
    uint32_t id_ = 0;
};

} // namespace xolver
