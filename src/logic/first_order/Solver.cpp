#include "logic/first_order/Solver.h"

namespace xolver::logic::first_order {
SolverAnswer solve(const Roots& roots, std::span<Backend* const> backends) {
    const auto features = nativeFeatures(roots);
    SolverAnswer unsupported;
    if (features.spatial) {
        unsupported.reason = "spatial operators require an explicit separation-logic request";
        return unsupported;
    }
    for (auto* backend : backends)
        if (backend && backend->accepts(roots, features)) return backend->solve(roots);
    if (features.function || features.otherSort)
        unsupported.reason = "first-order backend for functions or non-arithmetic sorts is not implemented";
    else if (features.real)
        unsupported.reason = "first-order real or mixed arithmetic backend is not implemented";
    else
        unsupported.reason = "no first-order theory backend accepts this input";
    return unsupported;
}
} // namespace xolver::logic::first_order
