#pragma once

// Capability 1 — Active Affine Substitution.
//
// Eliminates a variable defined by an active affine equality, substituting it
// throughout the remaining atoms (on RationalPolynomial copies; the IR is
// untouched).  When a substitution collapses an atom to a constant, the
// relation is decided: a violated constant is a DerivedConflict, a satisfied
// one marks the atom done.
//
// Sort discipline (plan §Cap. 1):
//   - Real LHS: any rational-coefficient affine equality is substituted.
//   - Int  LHS: ONLY unit-coefficient (±1) integer-affine equalities, so the
//     substitution preserves integer feasibility.  Non-unit Int equalities
//     (e.g. 2x = y+1) are left for Cap. 5 (HNF/SNF) to handle.

#include "theory/arith/presolve/Presolve.h"

namespace zolver {

class AffineSubstitution : public PresolveCapability {
public:
    const char* name() const override { return "AffineSubstitution"; }
    bool run(PresolveState& st) override;
};

} // namespace zolver
