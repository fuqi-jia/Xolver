#pragma once

// Capability 2 — Polynomial Definition Substitution.
//
// For an active equality that defines a variable v as a polynomial in the other
// variables (v appears only in the linear monomial {(v,1)}, no cross terms,
// unit coefficient for Int), substitutes v ↦ p throughout the remaining atoms.
// A resulting univariate atom is then handled by Cap. 4; a collapsed constant
// by registerSubstitution.  Bounded by MaxTermBudget = 256 monomials.

#include "theory/arith/presolve/Presolve.h"

namespace nlcolver {

class PolynomialDefSubstitution : public PresolveCapability {
public:
    const char* name() const override { return "PolynomialDefSubstitution"; }
    bool run(PresolveState& st) override;

    static constexpr size_t kMaxTermBudget = 256;
};

} // namespace nlcolver
