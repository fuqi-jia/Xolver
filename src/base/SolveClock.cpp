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
}

bool hasDeadline() {
    return g_budgetMs > 0 && g_startNs != 0;
}

long elapsedMs() {
    long long start = g_startNs;
    if (start == 0) return 0;
    return static_cast<long>((nowNs() - start) / 1000000LL);
}

long remainingMs() {
    if (!hasDeadline()) return NO_DEADLINE;
    long rem = g_budgetMs - elapsedMs();
    return rem > 0 ? rem : 0;
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
