#include "theory/arith/interval/ReasonedBoxQ.h"
#include <algorithm>

namespace nlcolver {

std::optional<ReasonedIntervalQ> ReasonedBoxQ::get(const std::string& var) const {
    auto it = box_.find(var);
    if (it == box_.end()) return std::nullopt;
    return it->second;
}

void ReasonedBoxQ::set(const std::string& var, ReasonedIntervalQ ri) {
    box_[var] = std::move(ri);
}

bool ReasonedBoxQ::narrow(const std::string& var, IntervalQ newInterval,
                         const std::vector<SatLit>& reasons) {
    auto it = box_.find(var);
    if (it == box_.end()) {
        box_[var] = ReasonedIntervalQ{newInterval, reasons};
        return true;
    }

    auto& ri = it->second;
    mpq_class newLo = std::max(ri.interval.lo, newInterval.lo);
    mpq_class newHi = std::min(ri.interval.hi, newInterval.hi);

    if (newLo > newHi) {
        ri.interval = IntervalQ{newLo, newHi};
        ri.reasons.insert(ri.reasons.end(), reasons.begin(), reasons.end());
        return true;
    }

    bool changed = (newLo != ri.interval.lo) || (newHi != ri.interval.hi);
    if (changed) {
        ri.interval = IntervalQ{newLo, newHi};
        ri.reasons.insert(ri.reasons.end(), reasons.begin(), reasons.end());
    }
    return changed;
}

bool ReasonedBoxQ::isEmpty() const {
    for (const auto& [var, ri] : box_) {
        if (ri.interval.isEmpty()) return true;
    }
    return false;
}

void ReasonedBoxQ::clear() {
    box_.clear();
}

const std::unordered_map<std::string, ReasonedIntervalQ>& ReasonedBoxQ::entries() const {
    return box_;
}

} // namespace nlcolver
