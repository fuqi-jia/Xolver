#pragma once

// Capability 3 — Polynomial Equality Combination.
//
// Stream active polynomial equalities through exact sparse row elimination on
// degree-2-or-higher monomials. A row whose nonlinear part vanishes supplies an
// affine consequence (or a constant conflict). Exact source coefficients retain
// the original premises; affine inputs already present are not recombined.
// The shared presolve deadline interrupts only unpublished work.

#include "search/presolve/Presolve.h"

namespace xolver {

class PolynomialEqualityCombination : public PresolveCapability {
public:
    const char* name() const override { return "PolynomialEqualityCombination"; }
    bool run(PresolveState& st) override;
};

} // namespace xolver
