#include "base/CooperativeProgress.h"
#include <doctest/doctest.h>

using namespace xolver;

TEST_CASE("Cooperative progress: alternating service retains pending work") {
    using Clock = CooperativeProgress::Clock;
    auto now = Clock::time_point{};
    const auto quantum = std::chrono::seconds(5);
    unsigned calls = 0;
    CooperativeProgress progress(quantum, [&](auto deadline) {
        CHECK(deadline == now + quantum);
        now = deadline;
        return ++calls == 2 ? CooperativeProgress::Step::Finished :
                              CooperativeProgress::Step::Pending;
    }, [&] { return now; });
    progress.poll();
    CHECK(calls == 0);
    now += quantum;
    progress.poll();
    CHECK(calls == 1);
    CHECK(progress.pending());
    progress.poll();
    CHECK(calls == 1);
    now += quantum;
    progress.poll();
    CHECK(calls == 2);
    CHECK_FALSE(progress.pending());
    now += quantum;
    progress.poll();
    CHECK(calls == 2);
}

TEST_CASE("Cooperative progress: inherited deadline and cancellation take priority") {
    using Clock = CooperativeProgress::Clock;
    auto now = Clock::time_point{};
    const auto quantum = std::chrono::seconds(5);
    unsigned calls = 0;
    CooperativeProgress progress(quantum, [&](auto deadline) {
        CHECK(deadline == now + std::chrono::seconds(1));
        ++calls;
        return CooperativeProgress::Step::Pending;
    }, [&] { return now; });
    now += quantum;
    progress.poll(now);
    CHECK(calls == 0);
    CHECK(progress.pending());
    progress.poll(now + std::chrono::seconds(1));
    CHECK(calls == 1);
    progress.cancel();
    now += quantum;
    progress.poll();
    CHECK(calls == 1);
}

TEST_CASE("Cooperative progress: nested polls do not reenter a running task") {
    using Clock = CooperativeProgress::Clock;
    auto now = Clock::time_point{};
    unsigned calls = 0;
    CooperativeProgress* active = nullptr;
    CooperativeProgress progress(std::chrono::seconds(1), [&](auto) {
        ++calls;
        active->poll();
        return CooperativeProgress::Step::Finished;
    }, [&] { return now; });
    active = &progress;
    now += std::chrono::seconds(1);
    progress.poll();
    CHECK(calls == 1);
    CHECK_FALSE(progress.pending());
}
