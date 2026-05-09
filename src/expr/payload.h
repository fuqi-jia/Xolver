#pragma once

#include <cstdint>
#include <string>
#include <variant>

namespace nlcolver {

/**
 * Leaf payload for CoreExpr: constant values and symbol names.
 * Kept simple — no GMP types here to avoid header bloat.
 * Rational constants stored as normalized strings ("1/3").
 */
struct Payload {
    using Value = std::variant<
        std::monostate,   // no payload
        bool,             // bool const
        int64_t,          // int const
        std::string,      // rational string or symbol name
        uint64_t          // BV const
    >;
    Value value;

    Payload() = default;
    explicit Payload(bool b)           : value(b) {}
    explicit Payload(int64_t i)        : value(i) {}
    explicit Payload(std::string s)    : value(std::move(s)) {}
    explicit Payload(uint64_t bv)      : value(bv) {}

    bool empty() const {
        return std::holds_alternative<std::monostate>(value);
    }
};

} // namespace nlcolver
