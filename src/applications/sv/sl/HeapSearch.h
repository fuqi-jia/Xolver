#pragma once
#include "contracts/SeparationFormula.h"

namespace xolver::sl::detail {
// Search only the heap, holding every location interpretation fixed. The
// caller prepares the formula once and owns the work budget across all stack
// candidates. Nil must map to 0; other class values need not be consecutive.
// Invalid stacks and search exhaustion throw Stop; incomplete witness checking
// returns Unknown. A SAT result includes a checked heap and preserves the
// supplied stack. UNSAT rules out this stack, not the original formula.
Outcome solveHeap(const Prepared&, const std::map<Location, uint64_t>&, Work&);
// Equality-only arrangement enumeration, using the same caller-owned budget.
Outcome solveArrangements(const Prepared&, Work&);
} // namespace xolver::sl::detail
