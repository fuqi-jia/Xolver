#include "proof/TheoryProofSink.h"

namespace xolver {
namespace proof {

// Single-threaded solve (CLAUDE.md): a thread-local pointer is a routing-free way
// for deep theory solvers to reach the per-solve collector the Solver owns,
// without threading a handle through every constructor. Cleared by the Solver
// after the solve. This carries no soundness weight — Carcara is the gate.
namespace {
thread_local TheoryProofSink* g_activeSink = nullptr;
}

TheoryProofSink* activeProofSink() { return g_activeSink; }
void setActiveProofSink(TheoryProofSink* sink) { g_activeSink = sink; }

} // namespace proof
} // namespace xolver
