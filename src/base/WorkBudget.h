#pragma once
#include "base/SolveClock.h"
#include <cstddef>
#include <limits>
#include <stdexcept>

namespace xolver {
struct ResourceExhausted : std::runtime_error { using std::runtime_error::runtime_error; };
class WorkBudget {
    std::size_t limit_, used_ = 0;
public:
    explicit WorkBudget(std::size_t limit = 2000000) : limit_(limit) {}
    void tick(std::size_t amount = 1) {
        if (amount > std::numeric_limits<std::size_t>::max() - used_ ||
            (limit_ && amount > limit_ - used_))
            throw ResourceExhausted("work budget exhausted");
        used_ += amount;
        if (wall::hasDeadline() && wall::remainingMs() == 0)
            throw ResourceExhausted("wall-clock budget exhausted");
    }
};
}
