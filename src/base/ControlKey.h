#pragma once

namespace xolver::config {
// Presence diagnostics intentionally differ from Boolean algorithm controls.
// File destinations, budgets and strategies never expose raw configuration text.
enum class ReadKind {
    Flag, Presence, Int, Long, Double,
    Boolean, Path, ProfilePath, Period, Capacity, Moduli, Projection
};
template<ReadKind Kind>
class Key {
public:
    explicit constexpr Key(const char* name) : name_(name) {}
    constexpr const char* name() const { return name_; }
private:
    const char* name_;
};
} // namespace xolver::config
