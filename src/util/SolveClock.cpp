#include "util/SolveClock.h"

#include <atomic>
#include <chrono>

namespace xolver {
namespace wall {
namespace {

// steady_clock nanoseconds at beginSolve(); 0 => no active solve.
// Atomic so the portfolio watchdog thread (Solver.cpp) can read remainingMs()
// concurrently with the solve thread without a data race.
std::atomic<long long> g_startNs{0};
std::atomic<long> g_budgetMs{0}; // <= 0 => no deadline

long long nowNs() {
    return std::chrono::duration_cast<std::chrono::nanoseconds>(
               std::chrono::steady_clock::now().time_since_epoch())
        .count();
}

} // namespace

void beginSolve(long totalBudgetMs) {
    g_budgetMs.store(totalBudgetMs, std::memory_order_relaxed);
    g_startNs.store(nowNs(), std::memory_order_relaxed);
}

void endSolve() {
    g_startNs.store(0, std::memory_order_relaxed);
    g_budgetMs.store(0, std::memory_order_relaxed);
}

bool hasDeadline() {
    return g_budgetMs.load(std::memory_order_relaxed) > 0 &&
           g_startNs.load(std::memory_order_relaxed) != 0;
}

long elapsedMs() {
    long long start = g_startNs.load(std::memory_order_relaxed);
    if (start == 0) return 0;
    return static_cast<long>((nowNs() - start) / 1000000LL);
}

long remainingMs() {
    if (!hasDeadline()) return NO_DEADLINE;
    long rem = g_budgetMs.load(std::memory_order_relaxed) - elapsedMs();
    return rem > 0 ? rem : 0;
}

} // namespace wall
} // namespace xolver
