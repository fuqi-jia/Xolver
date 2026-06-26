#pragma once

// Capability 11 — Nonnegative Polynomial Bound Extractor.
//
// For an active equality Σ tⱼ = C or upper inequality Σ tⱼ ≤ C in which every
// non-constant monomial tⱼ is manifestly non-negative (non-negative coefficient
// and all even exponents), derives:
//   - a negative-RHS DerivedConflict when C < 0;
//   - per-term upper bounds tⱼ ≤ C, and for single-variable even-power terms
//     c·x^e a symmetric variable bound −⌊(C/c)^(1/e)⌋ ≤ x ≤ ⌊(C/c)^(1/e)⌋
//     (integer e-th root) fed via addBound.
//
// The ≥ direction is NOT symmetric and is ignored (a lower bound on the sum
// says nothing about any single term).

#include "theory/arith/kernel/presolve/Presolve.h"

namespace xolver {

class NonnegativePolynomialBoundExtractor : public PresolveCapability {
public:
    const char* name() const override { return "NonnegativePolynomialBoundExtractor"; }
    bool run(PresolveState& st) override;
};

} // namespace xolver
