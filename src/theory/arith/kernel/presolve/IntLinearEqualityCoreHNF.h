#pragma once

// Capability 5 (Int) — Exact Linear Equality Core via Smith Normal Form.
//
// Collects the active integer linear equalities, builds the integer system
// A·x = b, and computes U·A·V = D (Smith Normal Form).  From this it derives:
//   - existence conflicts (d_i ∤ b'_i, or a zero row with b'_i ≠ 0);
//   - fixed-variable values (parameter-free lattice rows) via DerivedFixedValue
//     / registerSubstitution;
//   - congruence consequences (lattice rows with gcd > 1).
//
// Only active when the domain is Int (NIA).  No Int substitution leaves this
// core except parameter-free (fixed) values — matching Cap. 1's discipline.

#include "theory/arith/kernel/presolve/Presolve.h"

namespace xolver {

class IntLinearEqualityCoreHNF : public PresolveCapability {
public:
    const char* name() const override { return "IntLinearEqualityCoreHNF"; }
    bool run(PresolveState& st) override;
};

} // namespace xolver
