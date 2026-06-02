// Farkas-Or Phase 3: assemble a concrete integer model from a CSP
// assignment.
//
// Inputs: FarkasOrAssignment (B + choice + per-block λ ray + CT interval)
// + FarkasProfile (knows lambdas + outer assertions + boundedGlobals).
//
// Output: IntegerModel that pins every variable referenced by the
// formula. Bounded globals come from B; λ's come from the per-block ray;
// CT-like vars get pinned to a concrete value inside their interval
// (preferring the inclusive lower bound); residual vars (those that
// appear in outer assertions but not yet assigned) default to 0.
//
// The model is a *candidate*: Phase 4 validates it via ArithModelValidator
// against the original CoreIr formula before returning SAT.

#pragma once

#include "expr/ir.h"
#include "theory/arith/nia/farkas/FarkasOrSolver.h"
#include "theory/arith/nia/search/IntegerModelValidator.h"
#include <optional>

namespace xolver::farkas {

class FarkasOrModelAssembler {
public:
    explicit FarkasOrModelAssembler(const CoreIr& ir) : ir_(ir) {}

    // Build an IntegerModel from the CSP assignment. Returns nullopt if
    // the model cannot be assembled (e.g. empty CT interval after CSP).
    std::optional<IntegerModel> assemble(
        const FarkasProfile& profile,
        const FarkasOrAssignment& assignment) const;

private:
    const CoreIr& ir_;

    // Collect every Variable name referenced by an outer assertion (for
    // the residual-var = 0 default).
    std::unordered_set<std::string> collectFreeVars(
        const FarkasProfile& profile) const;
};

} // namespace xolver::farkas
