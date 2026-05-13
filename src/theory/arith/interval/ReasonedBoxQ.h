#pragma once

#include "theory/arith/interval/IntervalQ.h"
#include "theory/TheorySolver.h"
#include <string>
#include <unordered_map>
#include <optional>

namespace nlcolver {

/**
 * ReasonedIntervalQ: an IntervalQ together with SAT literal reasons.
 */
struct ReasonedIntervalQ {
    IntervalQ interval;
    std::vector<SatLit> reasons;
};

/**
 * ReasonedBoxQ: a box of per-variable rational intervals, each carrying SAT literal reasons.
 */
class ReasonedBoxQ {
public:
    std::optional<ReasonedIntervalQ> get(const std::string& var) const;
    void set(const std::string& var, ReasonedIntervalQ ri);
    bool narrow(const std::string& var, IntervalQ newInterval,
                const std::vector<SatLit>& reasons);
    bool isEmpty() const;
    void clear();
    const std::unordered_map<std::string, ReasonedIntervalQ>& entries() const;

private:
    std::unordered_map<std::string, ReasonedIntervalQ> box_;
};

} // namespace nlcolver
