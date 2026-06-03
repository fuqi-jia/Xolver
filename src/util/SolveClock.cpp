#include "util/SolveClock.h"

#include <atomic>
#include <chrono>

#include "util/EnvParam.h"

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

namespace {
// Read once: the autotuner / competition wrapper sets this before launch.
bool scaleEnabled() {
    static const bool e = env::paramInt("XOLVER_WALLCLOCK_SCALE", 0) != 0;
    return e;
}
} // namespace

long scaledBudgetMs(long baseMs, int shareNum, int shareDen) {
    // baseMs <= 0 is an "unlimited" sentinel in several budgets — never cap it.
    if (baseMs <= 0) return baseMs;
    if (!scaleEnabled() || !hasDeadline() || shareDen <= 0) return baseMs;
    long rem = remainingMs();
    if (rem <= 0) return baseMs; // deadline gone: keep the engine's own cutoff
    long share = (rem / shareDen) * shareNum; // divide first to avoid overflow
    if (share < baseMs) share = baseMs;       // at least the original budget
    if (share > rem) share = rem;             // never exceed time remaining
    return share;
}

long scaledCount(long base, long referenceMs, long maxMult) {
    if (base <= 0) return base;
    if (!scaleEnabled() || !hasDeadline()) return base;
    if (referenceMs <= 0 || maxMult <= 0) return base;
    long rem = remainingMs();
    if (rem <= 0) return base;
    // scaled = base * rem / referenceMs, in long long to avoid mid-mul overflow
    // on the kinds of caps we use (counts up to ~2^29 × budgets up to ~10^7 ms
    // fit comfortably in long long on every supported platform).
    long long scaled = (static_cast<long long>(base) * rem) / referenceMs;
    long long capped = static_cast<long long>(base) * maxMult;
    if (scaled < base) scaled = base;
    if (scaled > capped) scaled = capped;
    return static_cast<long>(scaled);
}

} // namespace wall
} // namespace xolver
