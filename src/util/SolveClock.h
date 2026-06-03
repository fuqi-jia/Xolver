#pragma once

namespace xolver {
namespace wall {

// Process-global solve wall-clock. Lets the solver's per-engine budgets scale
// to the time actually remaining instead of using isolated hardcoded cutoffs,
// so the solver can use its full competition timeout rather than giving up
// early (P0-A; see docs/REMEDIATION-SMTCOMP-FINAL.md §1).
//
// FOUNDATION ONLY. By itself this changes nothing: the deadline is unset by
// default, so remainingMs() == NO_DEADLINE (effectively infinite) and every
// consumer behaves exactly as before. The deadline is set once at solve entry
// from XOLVER_WALLCLOCK_MS (which run.sh / the competition wrapper can pass);
// 0 or unset => no deadline.
//
// Wiring budgets to actually scale against remainingMs() is a SEPARATE,
// panda-gated change — it alters verdicts/timing and must be measured on the
// differential harness, never flipped blind on WSL.

constexpr long NO_DEADLINE = -1;

// Begin a solve with `totalBudgetMs` of wall-clock (<= 0 => no deadline).
void beginSolve(long totalBudgetMs);

// End the current solve (clears the deadline). Optional — the next
// beginSolve() resets the clock — but call it for cleanliness so a stale
// deadline never leaks between solves on an incremental instance.
void endSolve();

// True iff a positive budget is set and a solve is active.
bool hasDeadline();

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

} // namespace wall
} // namespace xolver
