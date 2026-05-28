#pragma once

// Capability 3 — Polynomial Equality Combination.
//
// Given a set of active polynomial equalities {p₁=0,…,pₖ=0}, builds the
// coefficient submatrix E_high over the degree-≥2 monomials, computes the LEFT
// null-space basis over Q (vectors λ with λᵀ E_high = 0), and for each basis
// vector emits the linear consequence Σ λᵢ pᵢ (guaranteed degree ≤ 1) as a new
// equality atom for Cap. 5 / Cap. 1.  Sound because each pᵢ = 0.

#include "theory/arith/presolve/Presolve.h"

namespace xolver {

class PolynomialEqualityCombination : public PresolveCapability {
public:
    const char* name() const override { return "PolynomialEqualityCombination"; }
    bool run(PresolveState& st) override;
};

} // namespace xolver
