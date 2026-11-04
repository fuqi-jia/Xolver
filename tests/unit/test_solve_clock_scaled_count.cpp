// wall::scaledCount — count-shaped wall-clock scaling helper.
//
// This test pins the default-inert contract: with XOLVER_WALLCLOCK_SCALE unset
// (the production default) AND/OR no active deadline, scaledCount() returns
// the base value unchanged. That contract is what guarantees the plumbing
// change in BoundedNiaSolver / ModularResidueReasoner is verdict-neutral
// under the default configuration, so existing regression results are
// preserved while the autotuner-controlled scale path remains available.
//
// Scaled-path arithmetic (when both gates are open) is exercised via the
// per-cap end-to-end tests (autotuner sweep + competition differential), not
// here — the unit suite cannot reliably mutate the cached scaleEnabled() bit
// at runtime, and the math is short enough to inspect by review.

#include <doctest/doctest.h>

#include "base/SolveClock.h"
#include <xolver/Solver.h>
#include <limits>
#include <thread>

using namespace xolver;

TEST_CASE("wall::deadline scopes inherit an absolute deadline and restore after exceptions") {
    using Clock = std::chrono::steady_clock;
    wall::endSolve();
    CHECK(wall::deadline() == Clock::time_point::max());
    wall::beginSolve(60000);
    const auto parent = wall::deadline();
    CHECK(wall::deadline() == parent);
    {
        wall::DeadlineScope longer(Clock::time_point::max());
        CHECK(wall::deadline() == parent);
        const auto child = parent - std::chrono::seconds(1);
        try {
            wall::DeadlineScope shorter(child);
            CHECK(wall::deadline() == child);
            throw 1;
        } catch (int) {}
        CHECK(wall::deadline() == parent);
    }
    CHECK(wall::deadline() == parent);
    wall::endSolve();
}

TEST_CASE("wall::deadline scope works without a feature gate and bounds nested solves") {
    using Clock = std::chrono::steady_clock;
    wall::endSolve();
    const auto expired = Clock::now() - std::chrono::seconds(1);
    {
        wall::DeadlineScope outer(expired);
        CHECK(wall::hasDeadline());
        CHECK(wall::remainingMs() == 0);
        {
            // The public solver uses this guard around beginSolve/endSolve.
            wall::DeadlineScope nested;
            wall::beginSolve(60000);
            CHECK(wall::deadline() == expired);
            CHECK(wall::remainingMs() == 0);
            wall::endSolve();
        }
        CHECK(wall::deadline() == expired);
        CHECK(wall::remainingMs() == 0);
    }
    CHECK_FALSE(wall::hasDeadline());
    CHECK(wall::remainingMs() == wall::NO_DEADLINE);
}

TEST_CASE("wall::deadline scopes remain local to their solve thread") {
    using Clock = std::chrono::steady_clock;
    wall::endSolve();
    const auto parent = Clock::now() - std::chrono::seconds(1);
    wall::DeadlineScope scope(parent);
    bool workerUnbounded = false, workerRestored = false;
    std::thread worker([&] {
        workerUnbounded = !wall::hasDeadline() && wall::deadline() == Clock::time_point::max();
        {
            wall::DeadlineScope child(Clock::now() - std::chrono::seconds(1));
            if (wall::remainingMs() != 0) workerUnbounded = false;
        }
        workerRestored = !wall::hasDeadline();
    });
    worker.join();
    CHECK(workerUnbounded);
    CHECK(workerRestored);
    CHECK(wall::deadline() == parent);
}

TEST_CASE("wall::deadline conversion saturates without extending a caller scope") {
    using Clock = std::chrono::steady_clock;
    wall::endSolve();
    wall::beginSolve(std::numeric_limits<long>::max());
    CHECK(wall::hasDeadline());
    CHECK(wall::deadline() > Clock::now());
    const auto requested = Clock::now() - std::chrono::seconds(1);
    {
        wall::DeadlineScope scope(requested);
        CHECK(wall::deadline() == requested);
        CHECK(wall::remainingMs() == 0);
    }
    CHECK(wall::remainingMs() > 0);
    wall::endSolve();
}

TEST_CASE("wall::deadline caller survives a public solver check") {
    using Clock = std::chrono::steady_clock;
    wall::endSolve();
    const auto caller = Clock::now() + std::chrono::hours(1);
    {
        wall::DeadlineScope scope(caller);
        Solver solver;
        CHECK((solver.checkSat() == Result::Sat));
        CHECK(wall::deadline() == caller);
        CHECK(wall::hasDeadline());
    }
    CHECK_FALSE(wall::hasDeadline());
}

TEST_CASE("wall::scaledCount returns base when no deadline is set") {
    wall::endSolve();
    CHECK(wall::scaledCount(1) == 1);
    CHECK(wall::scaledCount(10000) == 10000);
    CHECK(wall::scaledCount(1L << 18) == (1L << 18));
    CHECK(wall::scaledCount(1L << 24) == (1L << 24));
}

TEST_CASE("wall::scaledCount preserves the unlimited sentinel") {
    // base <= 0 means "no cap" in several callers — must never be rewritten,
    // regardless of clock or scale state.
    wall::endSolve();
    CHECK(wall::scaledCount(0) == 0);
    CHECK(wall::scaledCount(-1) == -1);

    wall::beginSolve(60000);
    CHECK(wall::scaledCount(0) == 0);
    CHECK(wall::scaledCount(-1) == -1);
    wall::endSolve();
}

TEST_CASE("wall::scaledCount is inert without XOLVER_WALLCLOCK_SCALE") {
    // An active deadline alone is not enough to enable scaling — the lever is
    // explicitly opt-in via XOLVER_WALLCLOCK_SCALE so production runs without
    // the autotuner-promoted flag behave identically to before.
    wall::beginSolve(60000);
    CHECK(wall::scaledCount(10000) == 10000);
    CHECK(wall::scaledCount(1L << 18) == (1L << 18));
    wall::endSolve();
}

TEST_CASE("wall::scaledCount rejects nonpositive reference or maxMult") {
    // Defensive: bogus parameters should never amplify the base — return it
    // unchanged so a miswired caller can never silently shrink a cap.
    wall::beginSolve(60000);
    CHECK(wall::scaledCount(10000, /*referenceMs=*/0) == 10000);
    CHECK(wall::scaledCount(10000, /*referenceMs=*/-1) == 10000);
    CHECK(wall::scaledCount(10000, /*referenceMs=*/60000, /*maxMult=*/0) == 10000);
    CHECK(wall::scaledCount(10000, /*referenceMs=*/60000, /*maxMult=*/-1) == 10000);
    wall::endSolve();
}
