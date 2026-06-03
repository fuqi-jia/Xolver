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

#include "util/SolveClock.h"

using namespace xolver;

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
