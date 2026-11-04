#include "base/RuntimeConfig.h"
#include "base/SolveClock.h"

#include <chrono>
#include <algorithm>
#include <limits>

#include "base/EnvParam.h"

namespace xolver {
namespace wall {
namespace {

// steady_clock nanoseconds at beginSolve(); 0 => no active solve.
// Every engine executes on its calling solve thread. Separate solvers must
// not overwrite or end one another's deadline. Portfolio watchdogs use the
// backend's explicit termination API rather than reading this clock.
thread_local long long g_startNs = 0;
thread_local long g_budgetMs = 0; // <= 0 => no deadline
thread_local auto g_overrideDeadline = std::chrono::steady_clock::time_point::max();

long long nowNs() {
    return std::chrono::duration_cast<std::chrono::nanoseconds>(
               std::chrono::steady_clock::now().time_since_epoch())
        .count();
}

} // namespace

void beginSolve(long totalBudgetMs) {
    g_budgetMs = totalBudgetMs;
    g_startNs = nowNs();
}

void endSolve() {
    g_startNs = 0;
    g_budgetMs = 0;
    g_overrideDeadline = std::chrono::steady_clock::time_point::max();
}

bool hasDeadline() {
    return (g_budgetMs > 0 && g_startNs != 0) ||
        g_overrideDeadline != std::chrono::steady_clock::time_point::max();
}

std::chrono::steady_clock::time_point deadline() {
    using Clock = std::chrono::steady_clock;
    auto result = g_overrideDeadline;
    if (g_budgetMs > 0 && g_startNs != 0) {
        const auto start = Clock::time_point(std::chrono::duration_cast<Clock::duration>(
            std::chrono::nanoseconds(g_startNs)));
        const auto capacity = std::chrono::duration_cast<std::chrono::milliseconds>(
            Clock::time_point::max() - start).count();
        const auto bounded = g_budgetMs > capacity ? Clock::time_point::max() :
            start + std::chrono::milliseconds(g_budgetMs);
        result = std::min(result, bounded);
    }
    return result;
}

DeadlineScope::DeadlineScope(std::chrono::steady_clock::time_point requested)
    : previousStartNs_(g_startNs), previousBudgetMs_(g_budgetMs),
      previousOverride_(g_overrideDeadline) {
    g_overrideDeadline = std::min(requested, deadline());
}

DeadlineScope::~DeadlineScope() {
    g_startNs = previousStartNs_;
    g_budgetMs = previousBudgetMs_;
    g_overrideDeadline = previousOverride_;
}

long elapsedMs() {
    long long start = g_startNs;
    if (start == 0) return 0;
    return static_cast<long>((nowNs() - start) / 1000000LL);
}

long remainingMs() {
    if (!hasDeadline()) return NO_DEADLINE;
    long remaining = g_budgetMs > 0 && g_startNs != 0
        ? std::max(0L, g_budgetMs - elapsedMs()) : NO_DEADLINE;
    if (g_overrideDeadline != std::chrono::steady_clock::time_point::max()) {
        const auto now = std::chrono::steady_clock::now();
        const auto milliseconds = g_overrideDeadline <= now ? 0 :
            std::chrono::ceil<std::chrono::milliseconds>(g_overrideDeadline - now).count();
        const auto scoped = static_cast<long>(std::min<decltype(milliseconds)>(
            milliseconds, std::numeric_limits<long>::max()));
        if (remaining == NO_DEADLINE || scoped < remaining) remaining = scoped;
    }
    return remaining;
}

namespace {
// Read once: the autotuner / competition wrapper sets this before launch.
bool scaleEnabled() {
    const bool e = config::read<config::ReadKind::Int>("XOLVER_WALLCLOCK_SCALE", 0) != 0;
    return e;
}
} // namespace

long scaledBudgetMs(long baseMs, int shareNum, int shareDen) {
    // baseMs <= 0 is an "unlimited" sentinel in several budgets — never cap it.
    if (baseMs <= 0) return baseMs;
    if (!scaleEnabled() || !hasDeadline() || shareDen <= 0 || shareNum <= 0) return baseMs;
    long rem = remainingMs();
    if (rem <= 0) return baseMs; // deadline gone: keep the engine's own cutoff
    // Products of two positive machine integers fit in unsigned __int128.
    // Clamp before narrowing, including budgets supplied as LONG_MAX.
    auto wide = static_cast<unsigned __int128>(rem) * shareNum / shareDen;
    long share = static_cast<long>(std::min(wide,
        static_cast<unsigned __int128>(std::numeric_limits<long>::max())));
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
    auto scaled = static_cast<unsigned __int128>(base) * rem / referenceMs;
    auto capped = static_cast<unsigned __int128>(base) * maxMult;
    capped = std::min(capped, static_cast<unsigned __int128>(std::numeric_limits<long>::max()));
    if (scaled < base) scaled = base;
    if (scaled > capped) scaled = capped;
    return static_cast<long>(scaled);
}

} // namespace wall
} // namespace xolver
