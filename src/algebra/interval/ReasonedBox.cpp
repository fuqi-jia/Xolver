#include "algebra/interval/ReasonedBox.h"
#include <algorithm>

namespace xolver {
namespace {
void mergeReasons(std::vector<SatLit>& target, const std::vector<SatLit>& source) {
    target.insert(target.end(), source.begin(), source.end());
    std::sort(target.begin(), target.end(), [](SatLit a, SatLit b) {
        return a.var != b.var ? a.var < b.var : a.sign < b.sign;
    });
    target.erase(std::unique(target.begin(), target.end()), target.end());
}
}

std::optional<ReasonedInterval> ReasonedBox::get(const std::string& var) const {
    auto it = box_.find(var);
    if (it == box_.end()) return std::nullopt;
    return it->second;
}

void ReasonedBox::set(const std::string& var, ReasonedInterval ri) {
    box_[var] = std::move(ri);
}

bool ReasonedBox::narrow(const std::string& var, IntervalZ newInterval,
                         const std::vector<SatLit>& reasons) {
    auto it = box_.find(var);
    if (it == box_.end()) {
        box_[var] = ReasonedInterval{newInterval, reasons};
        return true;
    }

    auto& ri = it->second;
    mpz_class newLo = std::max(ri.interval.lo, newInterval.lo);
    mpz_class newHi = std::min(ri.interval.hi, newInterval.hi);

    if (newLo > newHi) {
        ri.interval = IntervalZ{newLo, newHi};
        mergeReasons(ri.reasons, reasons);
        return true;
    }

    bool changed = (newLo != ri.interval.lo) || (newHi != ri.interval.hi);
    if (changed) {
        ri.interval = IntervalZ{newLo, newHi};
        mergeReasons(ri.reasons, reasons);
    }
    return changed;
}

bool ReasonedBox::isEmpty() const {
    for (const auto& [var, ri] : box_) {
        if (ri.interval.isEmpty()) return true;
    }
    return false;
}

void ReasonedBox::clear() {
    box_.clear();
}

const std::unordered_map<std::string, ReasonedInterval>& ReasonedBox::entries() const {
    return box_;
}

} // namespace xolver
