#pragma once

#include <cstddef>
#include <functional>

namespace xolver {

// Execute with a larger stack when the host permits it. Prefer the main
// thread, temporarily raising its soft stack limit; otherwise use a joined
// worker with an explicit stack size. Resource failure falls back to the
// caller's existing stack. Temporary limits are restored, including on throw,
// and action exceptions propagate to the caller from either execution path.
void withExecutionStack(const std::function<void()>& action,
                        std::size_t minimumBytes = 512UL * 1024 * 1024);

} // namespace xolver
