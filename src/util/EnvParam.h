#pragma once

#include <iosfwd>

namespace xolver {
namespace env {

// Central reader for *tunable parameters* — budgets, caps, node-limits, and
// thresholds that have a good compile-time default but should remain
// externally configurable so the offline autotuner can sweep them and pick
// the best default. This is deliberately the OPPOSITE of the feature-flag
// elimination effort (docs/REMEDIATION-SMTCOMP-FINAL.md §2): feature flags
// get hardcoded/removed; budget parameters get centralized and kept tunable
// (§3 / the 2026-06-03 directive: "有 budget 的地方……变成外部可以配置的参数，
// 可以到时候用来选最好的默认参数").
//
// Every read is registered. Set XOLVER_DUMP_PARAMS=1 to have the complete
// knob surface (name, default, effective value, overridden?) printed to
// stderr at process exit — this is the autotuner's discovery list.
//
// Each parameter is read from the environment at most once per name and the
// result cached by the caller's `static const` (matching the existing
// `static const x = [](){...}()` idiom across the theory solvers), so these
// are zero-cost on the hot path after first use.

// Parse an integer parameter (base 10). Returns `def` if the env var is
// unset, empty, or unparseable.
long paramLong(const char* name, long def);
int  paramInt(const char* name, int def);

// Parse a floating-point parameter. Returns `def` if unset/empty/unparseable.
double paramDouble(const char* name, double def);

// Print every parameter read so far to `os`, one per line:
//   <name>\t<default>\t<effective>\t<overridden 0|1>
// Installed automatically as an atexit hook when XOLVER_DUMP_PARAMS is set;
// also callable directly (e.g. from a CLI `--dump-params`).
void dumpParams(std::ostream& os);

} // namespace env
} // namespace xolver
