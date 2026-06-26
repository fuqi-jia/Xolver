#pragma once

#include "theory/arith/kernel/poly/RationalPolynomial.h"
#include "sat/SatSolver.h"   // SatLit
#include "expr/types.h"      // Relation, VarId

#include <optional>
#include <vector>

namespace xolver {

// ============================================================================
// Positive-orthant sign-definiteness refuter (shared NRA/NIA).
//
// The Sturm-MBO QF_NRA family is "all variables positive ∧ a polynomial = 0",
// where the polynomial is a sum of monomials whose coefficients all share one
// sign. Such a polynomial is strictly sign-definite on the positive orthant
// (e.g. a sum of strictly-positive terms is > 0), so the equality is UNSAT —
// a trivial O(#monomials) argument, NOT cylindrical decomposition. (z3's
// general CAD times out; cvc5 does exactly this.)
//
// Given the active constraints, this:
//   1. derives each variable's sign (Pos/NonNeg/Neg/NonPos) from the single-
//      variable linear bounds present in the set;
//   2. for every other constraint  g rel 0, computes the definite sign of g
//      over that orthant (each monomial's sign is sign(coeff)·∏ sign(vᵢ)^{eᵢ});
//      if all monomials share one sign, g is sign-definite;
//   3. if that definite sign CONTRADICTS rel (e.g. g>0 vs g=0/≤0/<0), returns
//      the conflict — g's reason plus the bound reasons that fixed the signs.
//
// SOUNDNESS: it only ever reports a constraint that is provably impossible (a
// rigorous sign proof), so it can never produce a false UNSAT. nullopt = no
// refutation (caller continues). Pure: no kernel/engine dependency.
// ============================================================================

struct SignRefuteConstraint {
    RationalPolynomial poly;   // the constraint is  poly  rel  0
    Relation rel;
    SatLit reason;
};

// The conflict reason lits if some constraint is refuted by sign-definiteness;
// nullopt otherwise.
std::optional<std::vector<SatLit>>
refuteBySignDefiniteness(const std::vector<SignRefuteConstraint>& constraints);

} // namespace xolver
