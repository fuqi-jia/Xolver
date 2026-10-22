#pragma once

#include "ir/types.h"
#include "contracts/SatSolver.h"

namespace xolver {

/**
 * Thin interface for registering dynamically created theory atoms.
 * Breaks the circular dependency between TheoryAtomRegistry (theory/core)
 * and Atomizer (frontend/atomization).
 */
class DynamicAtomRegistrar {
public:
    virtual ~DynamicAtomRegistrar() = default;

    // Register a dynamically created theory atom (e.g. branch split, disequality split).
    // Returns the SAT literal. The exprId should be a synthetic id (not in NativeTerms).
    virtual SatLit registerDynamicAtom(ExprId expr, TheoryId theory) = 0;
};

} // namespace xolver
