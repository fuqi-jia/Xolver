#pragma once

#include "theory/arith/interval/IntervalTypes.h"
#include <string>
#include <unordered_map>
#include <optional>

namespace zolver {

/**
 * ReasonedBoxZ: a box of per-variable integer intervals, each carrying SAT literal reasons.
 *
 * Does NOT construct conflicts. The caller (e.g. NiaSolver adapter) is responsible
 * for assembling conflicts from violated constraints + used interval reasons.
 */
class ReasonedBoxZ {
public:
    // Get interval for a variable
    std::optional<ReasonedInterval> get(const std::string& var) const;

    // Set initial interval (e.g. from DomainStore)
    void set(const std::string& var, ReasonedInterval ri);

    // Narrow: intersect with new interval, merge reasons.
    // Returns true if interval actually changed.
    bool narrow(const std::string& var, IntervalZ newInterval,
                const std::vector<SatLit>& reasons);

    // Check if any interval is empty
    bool isEmpty() const;

    // Clear all intervals
    void clear();

    // Iterate over all entries
    const std::unordered_map<std::string, ReasonedInterval>& entries() const;

private:
    std::unordered_map<std::string, ReasonedInterval> box_;
};

} // namespace zolver
