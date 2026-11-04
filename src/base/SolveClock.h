#pragma once
#include <chrono>

namespace xolver {
namespace wall {

// Per-thread solve wall-clock. Solve entry sets the caller's timeout; nested
// proof/search helpers inherit its absolute deadline. Scoped caller limits
// may narrow that deadline and restore the parent clock when they leave.
// Zero or unset timeout means unbounded time. The legacy scaling helpers below
// retain their explicit configuration contract.

constexpr long NO_DEADLINE = -1;

// Begin a solve with `totalBudgetMs` of wall-clock (<= 0 => no deadline).
void beginSolve(long totalBudgetMs);

// End the current solve (clears the deadline). Optional — the next
// beginSolve() resets the clock — but call it for cleanliness so a stale
// deadline never leaks between solves on an incremental instance.
void endSolve();

// True iff a positive budget is set and a solve is active.
bool hasDeadline();

// Absolute deadline inherited by every stage of the current solve. An unset
// deadline is time_point::max(); helpers must not start an unrelated timer.
std::chrono::steady_clock::time_point deadline();

// A caller may narrow the current deadline, never extend it. Restore the full
// calling clock on exit, including exceptions and nested solver invocations.
class DeadlineScope {
    long long previousStartNs_;
    long previousBudgetMs_;
    std::chrono::steady_clock::time_point previousOverride_;
public:
    explicit DeadlineScope(std::chrono::steady_clock::time_point requested =
        std::chrono::steady_clock::time_point::max());
    ~DeadlineScope();
    DeadlineScope(const DeadlineScope&) = delete;
    DeadlineScope& operator=(const DeadlineScope&) = delete;
};

// Milliseconds elapsed since beginSolve(); 0 if no solve is active.
long elapsedMs();

// Milliseconds left until the deadline, clamped at 0. Returns NO_DEADLINE if
// no deadline is set — callers MUST treat NO_DEADLINE as "unbounded" and keep
// their existing default budget.
long remainingMs();

// Scale a per-engine budget to the wall-clock actually remaining, so the
// solver uses its full timeout instead of giving up at a flat hardcoded cutoff
// (the "2s of CAC then idle 1190s" problem). Returns `baseMs` UNCHANGED unless
// BOTH a deadline is set AND XOLVER_WALLCLOCK_SCALE is enabled — so by default
// this is inert and every consumer keeps its existing budget.
//
// When active: returns clamp(remainingMs()*shareNum/shareDen, baseMs,
// remainingMs()) — i.e. at least the original budget, at most the time left,
// typically a 1/shareDen slice of what remains. baseMs <= 0 (an "unlimited"
// sentinel) is returned unchanged. SOUND: only grows an engine's effort budget
// and never past the real deadline; never affects a verdict's correctness,
// only how long the engine is willing to search.
long scaledBudgetMs(long baseMs, int shareNum = 1, int shareDen = 4);

// Count-shaped sibling of scaledBudgetMs for enum/search caps that aren't
// natural ms (e.g. residue-enum size, cartesian-product cap). Returns `base`
// UNCHANGED unless BOTH a deadline is set AND XOLVER_WALLCLOCK_SCALE is
// enabled — so by default this is inert and every caller keeps its existing
// cap. base <= 0 (an "unlimited" sentinel) is returned unchanged.
//
// When active: returns clamp(base * remainingMs / referenceMs, base,
// base * maxMult). Intent: at `referenceMs` of remaining time, returns `base`;
// at 10x reference, returns ~10x base; saturates at `maxMult`x. With defaults
// (referenceMs=60_000, maxMult=32) a 1200s competition budget grows a cap by
// up to 20x at solve start, capped at 32x.
//
// SOUND for count caps: only ever GROWS the cap, never shrinks. A bigger cap
// means the same algorithm considers more candidates — never affects soundness,
// only completeness/coverage.
long scaledCount(long base, long referenceMs = 60000, long maxMult = 32);

} // namespace wall
} // namespace xolver
