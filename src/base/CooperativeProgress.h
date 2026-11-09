#pragma once

#include <algorithm>
#include <chrono>
#include <functional>
#include <stdexcept>
#include <utility>

namespace xolver {

// Alternate an already-yielded task with its caller on one thread. The task's
// measured initial service determines the quantum; there is no extra timeout
// or exhaustion verdict. The caller's absolute deadline always takes priority.
class CooperativeProgress {
public:
    using Clock = std::chrono::steady_clock;
    using Now = std::function<Clock::time_point()>;
    enum class Step { Pending, Finished };
    using Advance = std::function<Step(Clock::time_point)>;

    CooperativeProgress(Clock::duration quantum, Advance advance,
                        Now now = Clock::now)
        : quantum_(quantum), advance_(std::move(advance)), now_(std::move(now)) {
        if (quantum_ <= Clock::duration::zero())
            throw std::invalid_argument("cooperative service quantum must be positive");
        next_ = after(now_());
    }

    void poll(Clock::time_point deadline = Clock::time_point::max()) {
        if (!advance_ || running_) return;
        const auto start = now_();
        if (start < next_ || start >= deadline) return;
        struct Guard {
            bool& running;
            ~Guard() { running = false; }
        } guard{running_};
        running_ = true;
        auto advance = advance_;
        const auto step = advance(std::min(after(start), deadline));
        if (step == Step::Finished) cancel();
        else next_ = after(now_());
    }

    bool pending() const { return bool(advance_); }
    void cancel() { advance_ = {}; }

private:
    Clock::time_point after(Clock::time_point start) const {
        const auto remaining = Clock::time_point::max() - start;
        return quantum_ < remaining ? start + quantum_ : Clock::time_point::max();
    }
    Clock::duration quantum_;
    Advance advance_;
    Now now_;
    Clock::time_point next_;
    bool running_ = false;
};

} // namespace xolver
